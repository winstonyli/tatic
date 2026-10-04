use super::*;

// ---------------------------------------------------------------------
// Per-instance closure proof: covers a genuinely inconsistent closure-
// typed parameter (compile.rs's curried-dispatch capability), which
// `denote_closure` above can never cover -- it assigns one *static* type
// to each parameter, valid at *every* occurrence, which is precisely
// what an inconsistently-called parameter has none of.
//
// The fix isn't a bigger `Γ` -- there isn't a bigger one to have without
// a real dependent sum in the kernel's own type theory (a single honest
// type for "either `Clo_1` or `Clo_2`"), a separate, larger research
// question. Instead this follows *one concrete execution trace*: an
// `If`'s own condition is resolved concretely and only the taken branch
// is ever denoted (the same discipline `classify_step`/
// `prove_tail_recursive_call` already use for tail recursion, extended
// to closures), and a closure-typed variable's own call is resolved
// against whatever concrete literal lambda is *actually* bound there
// right now, dispatched at that call site's own concrete argument
// count -- never a statically-assigned one, since nothing here needs two
// different call sites for the same variable to agree on anything (a
// single concrete trace only ever reaches one of them). This makes the
// resulting proof a certificate for *one instance*, not a theorem
// covering every input -- the same honesty `prove_tail_recursive_call`
// already has, stated plainly rather than hidden.
//
// The one place this needs more than reading a postulate off a frame is
// *inlining*: when a literal-lambda-headed call's own declared parameter
// type disagrees with what a concretely-evaluated argument actually is
// (the `ArityUse::Inconsistent` case, from that callee's own
// perspective), `call_ref` cannot even be given a type for that
// parameter -- there is no opaque axiom to fall back on, so the only
// honest option is to substitute the concrete argument in and recurse
// into that callee's own body directly, faithfully modeling what both
// the `lower_wat` templates' own call convention and the interpreter's own
// substitution semantics actually do for that one call. No new
// postulate is introduced anywhere to do this -- every construction
// below reuses `call_ref`/`op_ref`/`register`/`mk_clo_ref`/`mk_env_ref`
// unchanged.

/// A closure value's own concrete identity, known at proof-construction
/// time for one specific instance: which literal lambda it is, and the
/// frame its own free variables (captures) resolve against. The second
/// part is the same two-frame discipline `eval_and_prove_call_over`/
/// `eval_and_prove_direct_call` already established for the `Int`-only
/// family (a closure's own captures always resolve against wherever it
/// was *created*, never wherever it's later called) -- without it, a
/// captured value read once a closure crosses a call boundary (a
/// parameter substituted in from an enclosing application) would resolve
/// against the wrong scope entirely.
pub(super) struct ConcreteClo {
    pub(super) root: Hash,
    pub(super) frame: Vec<DynVal>,
}

/// One frame slot's own concretely-known value, threaded through
/// `eval_dyn`'s walk -- the per-instance analogue of `denote_closure`'s
/// `params`/`param_types` pair. Every slot here holds an arbitrary compound
/// `Expr` rather than a bare postulate (contrast `denote_closure`'s
/// `params`): a substituted value (an inlined callee's own parameter, or a
/// closure's own captured value read back later) can be one, not a fresh,
/// unsubstituted postulate. Every `Int` slot also carries its own concrete
/// numeral, for concretely following an `If`'s own condition the same way
/// `classify_step` already does.
#[derive(Clone)]
pub(super) enum DynVal {
    Int(Expr, i64),
    Clo(Expr, Rc<ConcreteClo>),
}

/// `denote_closure`'s per-instance counterpart to `Denoted`: a `Clo` here
/// additionally carries its own `ConcreteClo` -- *which* literal lambda
/// this concretely is, and the frame to resolve its own captures against
/// -- since a per-instance proof, unlike the universal one, can actually
/// answer that question. `eval_dyn` frequently builds several of these
/// (e.g. one per argument at a call site) before they're all actually
/// consumed, holding each across further construction (`call_ref`, ...)
/// that may lazily push more postulates -- safe since a pushed postulate
/// is a `Const` and shifts nothing (`RELATED_WORK.md` §69).
pub(super) enum DynDenoted {
    Int(Expr),
    Clo(Expr, Rc<ConcreteClo>),
}

/// Projects `frame` down to plain `i64`s, for `eval_concrete`'s own
/// `params: &[i64]` convention -- used only to resolve an `If`'s own
/// condition concretely. A `Clo` slot has no meaningful projection (a
/// well-typed condition never references one); `0` is an arbitrary
/// placeholder, never legitimately read -- if it somehow were, the
/// resulting proof attempt would fail `kernel::check` later rather than
/// silently proving something false, the same "sound, not complete"
/// tolerance this whole fragment already has for a malformed input.
pub(super) fn dyn_frame_concrete_ints(frame: &[DynVal]) -> Vec<i64> {
    frame.iter().map(|v| match v { DynVal::Int(_, n) => *n, DynVal::Clo(..) => 0 }).collect()
}

/// Rebuilds an `eval::Env` matching `frame`'s own `Var`-index convention
/// (`frame[i]` <-> `Var(i)`), recursively reconstructing a `Clo` slot's
/// own `eval::Value::Closure`/`Value::Rec` from its `ConcreteClo` (whose
/// `root` is always the exact `Abs`/`Rec` node `eval_dyn` last resolved
/// it from, and whose own `frame` is that closure's *creation* scope --
/// exactly the `(Env, Hash)` pair `eval::eval` itself builds when it first
/// evaluates that same `Term::Abs`/`Term::Rec` node). `eval::Env::push`
/// is private, so this constructs `Env::Cons` directly -- both variants
/// are `pub`, this is not reaching past an intended boundary.
pub(super) fn dyn_frame_to_env(store: &TermStore, frame: &[DynVal]) -> Option<eval::Env> {
    let mut env = eval::Env::default();
    for v in frame.iter().rev() {
        let value = match v {
            DynVal::Int(_, n) => eval::Value::Int(*n),
            DynVal::Clo(_, cc) => {
                let cc_env = dyn_frame_to_env(store, &cc.frame)?;
                match store.resolve(cc.root) {
                    Term::Abs(body) => eval::Value::Closure(cc_env, *body),
                    Term::Rec(inner) => eval::Value::Rec(cc_env, *inner),
                    _ => return None, // unreachable: ConcreteClo::root is always Abs/Rec
                }
            }
        };
        env = eval::Env::Cons(Rc::new((value, env)));
    }
    Some(env)
}

/// The concrete numeral `eval_dyn_tail_recursive`/`eval_dyn_direct_call`
/// need for a *newly computed* `Int`-typed argument (so a later branch
/// condition that depends on it stays evaluable) -- unlike `eval_concrete`
/// (used only for the pure-arithmetic conditions `classify_step` itself
/// resolves, which `build_node`'s `If`-arm restriction guarantees never
/// embed a call), this argument may itself be an application of a
/// concretely-known closure (e.g. a loop-carried `g(x)`), which
/// `eval_concrete`'s own fragment (`Var`/`Lit`/`Prim`/`If` only) can't
/// evaluate at all. Rather than re-derive a second concrete evaluator for
/// applications, this defers to the reference interpreter itself
/// (`eval::eval`) over an `Env` rebuilt from `frame` (`dyn_frame_to_env`)
/// -- the same ground truth this whole project already judges every
/// other representation against, so reusing it here needs no separate
/// argument for why it's correct.
pub(super) fn eval_concrete_dyn(store: &TermStore, h: Hash, frame: &[DynVal]) -> Option<i64> {
    let env = dyn_frame_to_env(store, frame)?;
    match eval::eval(store, &env, h).ok()? {
        eval::Value::Int(n) => Some(n),
        eval::Value::Closure(..) | eval::Value::Rec(..) => None,
    }
}

/// Projects `frame` down to a `denote_closure`-style `param_types`
/// slice, for `capture_sig`/`register`/`call_ref`'s own use -- a `Clo`
/// slot's own type is its concrete literal's own real arity (`compile
/// ::peel`), not a statically-assigned one, since a per-instance frame
/// has no other notion of a closure slot's type to offer.
pub(super) fn dyn_frame_param_types(store: &TermStore, frame: &[DynVal]) -> Option<Vec<Option<usize>>> {
    frame
        .iter()
        .map(|v| match v {
            DynVal::Int(..) => Some(None),
            DynVal::Clo(_, cc) => compile::peel(store, cc.root).map(|(a, _, _)| Some(a)),
        })
        .collect()
}

/// Collects every literal anywhere in `h`'s own reachable structure,
/// including inside a nested `Abs`/`Rec`'s own body -- unlike
/// `collect_literals`/`collect_literals_closure`, which both deliberately
/// treat a called or bare literal lambda as opaque (the universal proof
/// never denotes a callee's own body, so it never needs to). `eval_dyn`
/// might inline *any* literal lambda's own body (see this section's own
/// docs), so every literal reachable anywhere -- not just at the top
/// level -- needs to be pre-postulated (`ArithPostulates::lit`'s own
/// documented precondition: every literal a term uses must be postulated
/// before any `Var`-referencing postulate is pushed). Over-collecting
/// (from a body that turns out never to need inlining) is harmless --
/// `lit` is memoized -- so this doesn't try to predict which bodies
/// `eval_dyn` will actually descend into, just walks everything once.
pub(super) fn collect_literals_dyn(store: &TermStore, h: Hash, out: &mut Vec<i64>) {
    match store.resolve(h) {
        Term::Var(_) => {}
        Term::Lit(n) => {
            if !out.contains(n) {
                out.push(*n);
            }
        }
        Term::Prim(_, a, b) => {
            let (a, b) = (*a, *b);
            collect_literals_dyn(store, a, out);
            collect_literals_dyn(store, b, out);
        }
        Term::If(c, t, e) => {
            let (c, t, e) = (*c, *t, *e);
            collect_literals_dyn(store, c, out);
            collect_literals_dyn(store, t, out);
            collect_literals_dyn(store, e, out);
        }
        Term::App(f, a) => {
            let (f, a) = (*f, *a);
            collect_literals_dyn(store, f, out);
            collect_literals_dyn(store, a, out);
        }
        Term::Abs(body) => collect_literals_dyn(store, *body, out),
        Term::Rec(inner) => collect_literals_dyn(store, *inner, out),
    }
}

/// Builds `mk_env(v_1,...,v_n)` for a combinator whose relative capture
/// indices are `captures`, reading each captured value's current value
/// directly out of `frame` -- the per-instance analogue of
/// `build_env_expr`, differing only in resolving each slot via `frame`'s
/// own `Expr` value rather than a raw postulate position (see `DynVal`'s
/// own docs for why a substituted slot may hold one).
pub(super) fn build_env_expr_dyn(store: &TermStore, combinators: &mut ClosureCombinators, captures: &[u32], frame: &[DynVal]) -> Option<Expr> {
    let frame_types = dyn_frame_param_types(store, frame)?;
    let sig = capture_sig(captures, &frame_types)?;
    let mut values = Vec::with_capacity(captures.len());
    for &rel in captures {
        let e = match frame.get(rel as usize)? {
            DynVal::Int(a, _) => a.clone(),
            DynVal::Clo(a, _) => a.clone(),
        };
        values.push(e);
    }
    let mk_env = combinators.cp.mk_env_ref(&sig);
    Some(apply_n(mk_env, values))
}

/// Bounds how much work following one concrete `eval_dyn` trace may do,
/// shared (via `&mut`) across the whole walk, including through mutual
/// recursion with `eval_dyn` itself (see its own docs). One counter: every
/// descent into a body costs a step -- an iteration of
/// `eval_dyn_tail_recursive`'s loop (which an embedded self-call also
/// enters), or `eval_dyn_inline_call` inlining a non-`Rec` combinator,
/// the one descent that loop never sees. So it bounds termination too: a
/// self-application reached only through a captured closure would
/// otherwise never stop.
///
/// This used to be three counters -- `tail_steps` (200) plus
/// `recursion_depth` (50) and `inline_call_depth` (25) -- because the
/// last two paths recurse through the native stack, and each was tuned
/// against a debug-build test thread's stack at a different per-level
/// cost. `eval_dyn` now runs through `kernel::grow` (`RELATED_WORK.md`
/// 32), so recursion depth is bounded by heap and all three reduce to
/// one cost bound.
pub(super) struct DynBudget {
    pub(super) steps: usize,
}

impl DynBudget {
    /// `steps` (and `prove_tail_recursive_call`'s `MAX_STEPS`, kept equal)
    /// was cut from 10,000 to 200 against two native-stack ceilings
    /// (`RELATED_WORK.md` §30): `kernel::check`'s recursion, and the
    /// recursive `Drop` of a discarded deep `Rc<Expr>` chain, which is
    /// what crashed `benches/execution.rs`. Both are gone now -- the
    /// kernel's traversals and `Expr`'s `Drop` run through
    /// `kernel::grow` (§31) -- so 200 is no longer a safety bound, only a
    /// cost one: each step deepens the accumulated expression, and
    /// checking it gets correspondingly slower. It has not been
    /// re-measured as a cost bound; raising it is §31's open item.
    pub(super) fn new() -> Self {
        DynBudget { steps: 200 }
    }
}

/// Follows one concrete trace through a `Rec`-wrapped, *tail*-recursive
/// `body` (`arity` params plus the self-reference at `Var(arity)`,
/// matching `peel`'s own convention), starting from `frame` -- the
/// per-instance, closure-capable sibling of `prove_tail_recursive_call`'s
/// own `classify_step` loop, reusing `classify_step` itself unchanged
/// (it only ever needs concrete `i64`s to pick a branch or recognize a
/// self-call, which `dyn_frame_concrete_ints` already projects `frame`
/// down to). This is what lets `eval_dyn_direct_call` inline a `root`
/// that's itself self-recursive: the *inconsistent*-arity closure
/// parameter this whole per-instance methodology exists for is exactly
/// as likely to be threaded, unchanged, through a tail-recursive loop as
/// to sit in a straight-line callee -- and `RELATED_WORK.md`'s own
/// "recursive use of curried dispatch has no kernel-proof coverage"
/// gap is precisely this case.
///
/// A *non*-tail self-call (embedded inside a larger expression, not
/// recognized by `classify_step`'s own `match_self_call`, which only
/// matches when the self-call is the *entire* remaining leaf) isn't
/// handled by this loop directly -- `eval_dyn` itself now recognizes one
/// (see its own docs) and calls back into this function, mutually
/// recursive, one Rust stack frame per embedded self-call actually
/// followed -- each of which re-enters this loop, and so costs a
/// `budget.steps` step like any other iteration.
///
/// `combinators`' `register`/`call_ref` memoization is keyed by `Hash`
/// alone (see `eval_dyn_direct_call`'s own docs on this) -- safe here as
/// long as any one literal reached from more than one iteration is
/// always denoted from the same frame each time, true whenever a
/// closure-typed parameter is simply threaded through the loop unchanged
/// (this function's own reason for existing) rather than replaced by a
/// freshly created one with different captures partway through.
pub(super) fn eval_dyn_tail_recursive(
    store: &TermStore,
    body: Hash,
    arity: usize,
    combinators: &mut ClosureCombinators,
    budget: &mut DynBudget,
    mut frame: Vec<DynVal>,
) -> Option<DynDenoted> {
    let self_idx = arity as u32;
    let self_ctx = Some((body, arity));

    loop {
        if budget.steps == 0 {
            return None;
        }
        budget.steps -= 1;
        let concrete = dyn_frame_concrete_ints(&frame);
        match classify_step(store, body, arity, self_idx, &concrete)? {
            StepOutcome::Base(leaf) => return eval_dyn(store, leaf, combinators, self_ctx, budget, &frame),
            StepOutcome::TailCall(arg_exprs) => {
                if arg_exprs.len() != arity {
                    return None;
                }
                let mut new_frame = Vec::with_capacity(arity);
                for i in 0..arity {
                    let expr = arg_exprs[arity - 1 - i];
                    let val = match eval_dyn(store, expr, combinators, self_ctx, budget, &frame)? {
                        DynDenoted::Int(e) => {
                            let n = eval_concrete_dyn(store, expr, &frame)?;
                            DynVal::Int(e, n)
                        }
                        DynDenoted::Clo(e, cc) => DynVal::Clo(e, cc),
                    };
                    new_frame.push(val);
                }
                frame = new_frame;
            }
        }
    }
}

/// Resolves a call to `root` (a literal lambda, or a named self-recursive
/// combinator) applied to `args` -- shared by both ways `eval_dyn`'s own
/// `App` handling reaches a literal callee: directly (`root_frame` is
/// whatever frame `root` was itself just found in, generally the same as
/// `calling_frame`) or through a closure-typed variable's own
/// `ConcreteClo` (`root_frame` is that closure's *own* creation frame,
/// genuinely different from `calling_frame` -- this function never
/// assumes they're the same). `args` are always evaluated against
/// `calling_frame` (wherever this call itself is being walked);
/// `root`'s own free variables (captures), if any, always resolve
/// against `root_frame` (wherever `root` itself was written) -- the same
/// two-frame discipline `ConcreteClo`'s own docs describe.
///
/// Scoped deliberately narrowly: only an exactly-saturated call (no
/// partial or over-application of `root` itself), and inlining -- always
/// needed when `root`'s own body concretely returns a further `Clo`
/// (`combinator_return_type`; there's no other way to learn *which*
/// concrete literal that is than to recurse into `root`'s own body), and
/// also needed whenever some argument's own concrete value is a `Clo`
/// but `root`'s static classification declined to type that parameter as
/// one -- only ever inlines a non-capturing `root` (`Rec`-wrapped or not
/// -- a `Rec`-wrapped `root` is traced through its own self-calls via
/// `eval_dyn_tail_recursive`, tail *or non-tail*, see its own and
/// `eval_dyn`'s own docs).
///
/// One more constraint worth being explicit about, found while verifying
/// this by deliberately feeding `call_ref` the wrong frame here and
/// confirming a test caught it (only one of two attempts actually did):
/// `call_ref`/`register`'s own memoization is keyed by `root`'s `Hash`
/// *alone*, never by which frame its captures resolve against -- sound
/// in `denote_closure`'s own world, where a single `param_types` is
/// fixed for one whole proof attempt, so every call site for the same
/// `root` necessarily agrees on it anyway. `eval_dyn`'s own frame
/// genuinely changes across a recursion (inlining swaps in a child
/// frame), so this function relies on every one of its own callers never
/// calling the *same* `root` from two genuinely different creation
/// frames within one proof attempt -- true of every shape the four
/// target tests exercise (each literal is denoted and called from
/// exactly one frame each), but not something this function -- or
/// `kernel::check` itself, which can't see past a self-consistently
/// wrong frame to know it disagrees with a different call site's own
/// correct one -- can catch on its own if a future generalization ever
/// violated it.
#[allow(clippy::too_many_arguments)]
pub(super) fn eval_dyn_direct_call(
    store: &TermStore,
    combinators: &mut ClosureCombinators,
    root: Hash,
    root_frame: &[DynVal],
    args: &[Hash],
    calling_self_ctx: Option<(Hash, usize)>,
    budget: &mut DynBudget,
    calling_frame: &[DynVal],
) -> Option<DynDenoted> {
    let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
    if args.len() != root_arity {
        return None;
    }
    let root_param_types = param_types_for(store, root)?;
    let return_ty = combinator_return_type(store, root).unwrap_or(None);
    // Computed once, up front, and shared by both branches below (the
    // opaque path needs it as `captures`; the inline path needs it for
    // its own scoping check) -- a pure function of `root`'s own static
    // structure alone, entirely independent of `args`' concrete values.
    // When `return_ty.is_some()`, `needs_inline` is unconditionally true
    // below regardless of what `args` evaluate to, so checking this
    // *before* evaluating any argument (each its own, possibly
    // expensive, recursive `eval_dyn` call building up a kernel proof
    // term) lets a `root` that's already known to fall outside this
    // function's own scoping restriction bail out for free, rather than
    // doing all that work only to discard it once `eval_dyn_inline_call`
    // makes the exact same check anyway.
    let captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
    if return_ty.is_some() && !captures.is_empty() {
        return None; // scoped out -- see eval_dyn_inline_call's own docs
    }

    let mut arg_vals = Vec::with_capacity(args.len());
    for &a in args {
        arg_vals.push(eval_dyn(store, a, combinators, calling_self_ctx, budget, calling_frame)?);
    }
    let needs_inline = return_ty.is_some()
        || arg_vals
            .iter()
            .enumerate()
            .any(|(j, v)| root_param_types[root_arity - 1 - j].is_none() && matches!(v, DynDenoted::Clo(..)));

    if needs_inline {
        return eval_dyn_inline_call(store, combinators, root_body, root_arity, root_is_rec, captures, arg_vals, args, calling_frame, budget);
    }

    // Ordinary opaque call: mirrors `denote_closure`'s own
    // `LitLambdaExact` construction exactly, just resolving `root`'s own
    // captures against `root_frame` instead of `params`.
    let root_frame_types = dyn_frame_param_types(store, root_frame)?;
    let call_fn = combinators.call_ref(root, &captures, &root_frame_types)?;
    let env_expr = if captures.is_empty() {
        None
    } else {
        let e = build_env_expr_dyn(store, combinators, &captures, root_frame)?;
        Some(e)
    };
    let mut arg_exprs = Vec::with_capacity(root_arity);
    for (j, v) in arg_vals.into_iter().enumerate() {
        let pos = root_arity - 1 - j;
        let e = match (root_param_types[pos], v) {
            // A closure of another arity can't be passed where a `Clo_k` is
            // expected (see `arg_denotation`).
            (Some(k), DynDenoted::Clo(e, cc)) if compile::peel(store, cc.root).map(|(a, _, _)| a) == Some(k) => e,
            (None, DynDenoted::Int(e)) => e,
            // An `Int` parameter given a `Clo` was inlined above.
            _ => return None,
        };
        arg_exprs.push(e);
    }
    let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
    if let Some(env_expr) = &env_expr {
        all_args.push(env_expr.clone());
    }
    all_args.extend(arg_exprs.iter().cloned());
    let applied = apply_n(call_fn, all_args);
    // `return_ty` was already checked above: `needs_inline` is true
    // whenever it's `Some`, so this opaque path -- reached only when
    // `needs_inline` was false -- always has a plain `Int` result here.
    debug_assert!(return_ty.is_none(), "a Clo-returning root should always have been inlined above");
    let int_ty = combinators.cp.arith.int_ty();
    let applied_resolved = applied.clone();
    debug_assert_has_type(&combinators.cp.arith.p, &applied_resolved, &int_ty, "eval_dyn: direct combinator call");
    Some(DynDenoted::Int(applied))
}

/// The recursive-continuation half of `eval_dyn_direct_call`'s own
/// `needs_inline` branch, out-of-lined (`#[inline(never)]`) so that
/// `eval_dyn_direct_call`'s own, already-sizeable locals (`arg_vals`,
/// `root_param_types`, etc. -- dead by this point, but still part of its
/// stack frame in an unoptimized build) don't inflate the per-level cost
/// of the mutual recursion this function feeds into
/// (`eval_dyn_inline_call` -> `eval_dyn`/`eval_dyn_tail_recursive` ->
/// `eval_dyn_direct_call` -> back into `eval_dyn_inline_call`, one real
/// native-stack round trip per inlined level). This extraction alone
/// turned out not to be sufficient, unlike `infer_sup`'s own precedent
/// (`kernel.rs`) it was modeled on: `eval_dyn_direct_call`'s own prologue
/// (`param_types_for`, `combinator_return_type`, and each argument's own
/// `eval_dyn` call, all before dispatch is even decided) stays live on
/// the stack for the whole nested call regardless of what's extracted out
/// of its tail, so a term built specifically to drive this path
/// (self-application reached only through a captured closure, not
/// `eval_dyn`'s own embedded-self-call recognition) still reliably
/// overflowed the native stack in an unoptimized debug-build test thread
/// at roughly the 43rd-45th level. That is why this path once had its
/// own, smaller depth counter; `eval_dyn` now runs through
/// `kernel::grow`, so depth here is bounded by heap and only
/// `DynBudget::steps` limits it.
///
/// `captures` is `root`'s own `free_vars` (`root_body`/`root_arity`/
/// `root_is_rec`), computed once by the caller rather than here: a pure
/// function of `root`'s static structure alone, so `eval_dyn_direct_call`
/// already needs it (to decide the *opaque*-call path's own captures) and
/// -- when `return_ty.is_some()` there, so this path is unconditionally
/// about to be taken regardless of `arg_vals` -- can check it *before*
/// spending the cost of evaluating every argument, rather than after.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
pub(super) fn eval_dyn_inline_call(
    store: &TermStore,
    combinators: &mut ClosureCombinators,
    root_body: Hash,
    root_arity: usize,
    root_is_rec: bool,
    captures: Vec<u32>,
    arg_vals: Vec<DynDenoted>,
    args: &[Hash],
    calling_frame: &[DynVal],
    budget: &mut DynBudget,
) -> Option<DynDenoted> {
    if !captures.is_empty() {
        return None; // scoped out -- see eval_dyn_direct_call's own docs
    }
    let mut child: Vec<Option<DynVal>> = vec![None; root_arity];
    for (j, (v, &a)) in arg_vals.into_iter().zip(args.iter()).enumerate() {
        let pos = root_arity - 1 - j;
        child[pos] = Some(match v {
            // `e` carries into the child frame unchanged, safe to resolve
            // however much more gets pushed in between.
            DynDenoted::Int(e) => {
                let n = eval_concrete_dyn(store, a, calling_frame)?;
                DynVal::Int(e, n)
            }
            DynDenoted::Clo(e, cc) => DynVal::Clo(e, cc),
        });
    }
    let child: Vec<DynVal> = child.into_iter().collect::<Option<Vec<_>>>()?;
    if root_is_rec {
        return eval_dyn_tail_recursive(store, root_body, root_arity, combinators, budget, child);
    }
    // A non-`Rec` body is the one descent `eval_dyn_tail_recursive`'s loop
    // never counts, so it costs its own step -- without this, mutual
    // recursion across combinators reached only through captured
    // closures would never terminate. See `DynBudget`.
    if budget.steps == 0 {
        return None;
    }
    budget.steps -= 1;
    eval_dyn(store, root_body, combinators, None, budget, &child)
}

/// Per-instance, closure-capable sibling of `denote_closure` -- see this
/// section's own module docs for the methodology and why it's needed.
/// `frame`'s own length must match whatever scope `h` is being evaluated
/// in (`Var(i)` resolves to `frame[i]`, the same convention
/// `denote_closure`'s `params`/`param_types` share).
///
/// `self_ctx`, when `Some((body, arity))`, means `h` is being walked
/// inside a `Rec`-wrapped combinator's own body (that same `body`/`arity`
/// pair), so `Var(arity)` there is a self-reference, exactly matching
/// `peel`'s own convention -- `None` in every other scope (a
/// non-recursive body, or once inlined into a *different* combinator's
/// own body via `eval_dyn_direct_call`, which computes the callee's own
/// fresh `self_ctx` rather than inheriting the caller's). This is what
/// lets a *non*-tail self-call (embedded inside a larger expression, not
/// recognized by `eval_dyn_tail_recursive`'s own `classify_step`, which
/// only matches when a self-call is the *entire* remaining leaf) still
/// be followed: the `App`/`Var` case below recognizes one directly and
/// calls back into `eval_dyn_tail_recursive`, mutually recursive with
/// this function, one more Rust stack frame per embedded self-call
/// actually reached, each costing a `budget.steps` step (see
/// `DynBudget`). A *branching*
/// non-tail shape (more than one self-call in the same leaf, e.g.
/// `f(n-1) + f(n-2)`) falls out of this for free -- each occurrence is
/// just another embedded self-call, evaluated independently -- but is
/// exponential in trace length the same way any per-instance trace of a
/// branching recursive shape is, so it's only practical for the small,
/// fixed samples this whole methodology is ever run against, never a
/// substitute for `prove_tail_recursive_universal`'s own genuine
/// induction on shapes it already covers.
///
/// Every cycle in that mutual recursion (`eval_dyn_tail_recursive`,
/// `eval_dyn_direct_call`, `eval_dyn_inline_call`) passes back through
/// here, so this one [`kernel::grow`] makes the whole family's depth
/// bounded by heap, not native stack.
pub(super) fn eval_dyn(store: &TermStore, h: Hash, combinators: &mut ClosureCombinators, self_ctx: Option<(Hash, usize)>, budget: &mut DynBudget, frame: &[DynVal]) -> Option<DynDenoted> {
    kernel::grow(|| eval_dyn_node(store, h, combinators, self_ctx, budget, frame))
}

/// [`eval_dyn`]'s body.
pub(super) fn eval_dyn_node(store: &TermStore, h: Hash, combinators: &mut ClosureCombinators, self_ctx: Option<(Hash, usize)>, budget: &mut DynBudget, frame: &[DynVal]) -> Option<DynDenoted> {
    let shape = match self_ctx {
        Some((_, self_arity)) => compile::classify(store, h, self_arity, Some(self_arity as u32)),
        None => compile::classify(store, h, frame.len(), None),
    };
    match shape {
        Shape::If(c, t, e) => {
            let concrete = dyn_frame_concrete_ints(frame);
            let cv = eval_concrete(store, c, &concrete)?;
            eval_dyn(store, if cv != 0 { t } else { e }, combinators, self_ctx, budget, frame)
        }
        Shape::SelfCall(args) => {
            // An embedded (non-tail) self-call -- see this function's
            // own docs.
            let (self_body, self_arity) = self_ctx?;
            let mut new_frame: Vec<Option<DynVal>> = vec![None; self_arity];
            for (j, &a) in args.iter().enumerate() {
                let pos = self_arity - 1 - j;
                let denoted = eval_dyn(store, a, combinators, self_ctx, budget, frame)?;
                new_frame[pos] = Some(match denoted {
                    DynDenoted::Int(e) => {
                        let n = eval_concrete_dyn(store, a, frame)?;
                        DynVal::Int(e, n)
                    }
                    DynDenoted::Clo(e, cc) => DynVal::Clo(e, cc),
                });
            }
            let new_frame: Vec<DynVal> = new_frame.into_iter().collect::<Option<Vec<_>>>()?;
            eval_dyn_tail_recursive(store, self_body, self_arity, combinators, budget, new_frame)
        }
        Shape::VarCall { var, args, .. } => {
            let DynVal::Clo(_, cc) = frame.get(var as usize)?.clone() else { return None };
            let cc_root = cc.root;
            let cc_frame = cc.frame.clone();
            eval_dyn_direct_call(store, combinators, cc_root, &cc_frame, &args, self_ctx, budget, frame)
        }
        Shape::CombinatorCall { root, args, .. } => eval_dyn_direct_call(store, combinators, root, frame, &args, self_ctx, budget, frame),
        Shape::OtherCall => None,
        Shape::Var(i) => {
            if let Some((_, self_arity)) = self_ctx
                && i as usize == self_arity
            {
                // A bare reference to the enclosing self-recursive value
                // itself, not applied -- out of scope structurally, the
                // same restriction `compile.rs`'s own `free_vars` places
                // on capturing a self-reference as a plain value from a
                // nested closure.
                return None;
            }
            match frame.get(i as usize)?.clone() {
                DynVal::Int(e, _) => Some(DynDenoted::Int(e)),
                DynVal::Clo(e, cc) => Some(DynDenoted::Clo(e, cc)),
            }
        }
        Shape::Lit(n) => Some(DynDenoted::Int(combinators.cp.arith.lit_ref(n))),
        Shape::Prim(op, a, b) => {
            let DynDenoted::Int(da) = eval_dyn(store, a, combinators, self_ctx, budget, frame)? else { return None };
            let DynDenoted::Int(db) = eval_dyn(store, b, combinators, self_ctx, budget, frame)? else { return None };
            let op_ref = combinators.cp.arith.op_ref(op); // pre-postulated once -- never pushes
            let applied = kernel::app2(op_ref, da, db);
            let int_ty = combinators.cp.arith.int_ty();
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "eval_dyn: Prim");
            Some(DynDenoted::Int(applied))
        }
        Shape::Combinator { .. } => {
            let (arity, body, is_rec) = compile::peel(store, h)?;
            if arity == 0 || is_rec {
                // A bare self-recursive value isn't needed by this
                // first slice's own target shapes -- decline cleanly
                // rather than build a `ConcreteClo` nothing here ever
                // dispatches through (a self-recursive callee is never
                // reached via `eval_dyn_direct_call`'s own opaque path,
                // which is the only consumer of a `ConcreteClo` at all).
                return None;
            }
            let captures = compile::free_vars(store, body, arity, is_rec);
            let frame_types = dyn_frame_param_types(store, frame)?;
            let sym = combinators.register(h, &captures, &frame_types)?;
            let cc = Rc::new(ConcreteClo { root: h, frame: frame.to_vec() });
            if captures.is_empty() {
                return Some(DynDenoted::Clo(sym, cc));
            }
            let env = build_env_expr_dyn(store, combinators, &captures, frame)?;
            let applied = kernel::app(sym, env);
            let clo_ty = combinators.cp.clo_ty(arity);
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "eval_dyn: capturing closure value");
            Some(DynDenoted::Clo(applied, cc))
        }
    }
}

/// Attempts a kernel-checked equivalence proof for *one specific call*
/// `h(args)` -- the per-instance sibling of `prove_closure_expr`, for
/// exactly the case that one can never cover: a closure-typed parameter
/// called with genuinely inconsistent arities across call sites (see
/// this section's own module docs for the methodology, and
/// `TYPES.md`/`RELATED_WORK.md` for why `denote_closure`'s own universal
/// approach is a dead end here without a real dependent sum in the
/// kernel).
///
/// Returns `None` for: an arity mismatch; any top-level parameter that
/// isn't plain `Int` (this project's own sampling battery, `jit.rs`'s
/// `sample_arg_vectors`/`eval::apply_term`, is `i64`-only, so a genuinely
/// `Clo`-typed top-level parameter was never something this regime could
/// exercise anyway -- a real but harmless scope line, not a workaround);
/// or anything `eval_dyn`/`eval_dyn_tail_recursive` itself declines (see
/// their own and `eval_dyn_direct_call`'s docs for exactly what that is
/// -- in particular, `h` itself `Rec`-wrapped is followed via
/// `eval_dyn_tail_recursive` whether its body is tail- or non-tail-
/// recursive, including a branching non-tail shape, via `self_ctx`).
pub fn prove_closure_expr_instance(store: &TermStore, h: Hash, args: &[i64]) -> Option<EquivalenceProof> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    if arity != args.len() {
        return None;
    }
    let top_param_types = param_types_for(store, h)?;
    if top_param_types.iter().any(Option::is_some) {
        return None;
    }

    let mut lits = Vec::new();
    collect_literals_dyn(store, body, &mut lits);

    let mut combinators = ClosureCombinators::new(store);
    for n in lits {
        combinators.cp.arith.lit(n);
    }

    // By-`Var`-index concrete params (`Var(0)` = last-applied), matching
    // `denote_closure`'s/`prove_tail_recursive_call`'s own convention.
    let mut frame = Vec::with_capacity(arity);
    for i in 0..arity {
        let n = args[arity - 1 - i];
        let int_ty = combinators.cp.arith.int_ty();
        let pos = combinators.cp.arith.p.push(int_ty);
        let e = combinators.cp.arith.p.get(pos);
        frame.push(DynVal::Int(e, n));
    }

    let mut budget = DynBudget::new();
    let denoted = if is_rec {
        eval_dyn_tail_recursive(store, body, arity, &mut combinators, &mut budget, frame)?
    } else {
        eval_dyn(store, body, &mut combinators, None, &mut budget, &frame)?
    };
    let (result_ty, denotation) = match denoted {
        DynDenoted::Int(e) => (combinators.cp.arith.int_ty(), e.clone()),
        DynDenoted::Clo(e, cc) => {
            let (k, _, _) = compile::peel(store, cc.root)?;
            let ty = combinators.cp.clo_ty(k);
            (ty, e.clone())
        }
    };
    let proof = kernel::refl(denotation.clone());
    let proof_ty = kernel::id(result_ty.clone(), denotation.clone(), denotation.clone());
    combinators.cp.arith.p.check(&proof, &proof_ty).ok()?;

    Some(EquivalenceProof {
        globals: combinators.cp.arith.p.globals,
        arity,
        result_ty,
        denotation,
        proof,
    })
}
