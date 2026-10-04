use super::*;

// --- closures (non-capturing, capturing, and partially-applied) ------------
//
// Mirrors `compile.rs`'s own closure-conversion reading (see its module
// docs) at the proof level, for the same fragment it compiles: a closed,
// non-recursive term whose body, plus every combinator it calls
// (capturing or not), is built from `Var`/`Lit`/`Prim`/`If` and
// fully-saturated applications of either a closure-typed parameter or a
// literal lambda -- exactly what
// `compile::unwind_app_spine`/`compile::infer_closure_arities` already
// classify, reused directly here rather than re-derived, so the two
// readings can't silently diverge on "what counts as a closure call".
//
// A closure value's type, for a given arity `k`, is `Clo_k`
// (`ClosurePostulates::clo_ty`) -- literally the curried Pi type `Int ->
// .. -> Int` (`k` copies), a real kernel type built from ordinary `Pi`
// nodes, *not* an opaque `Sort(0)` postulate the way `Int` itself is.
// Applying one *through a parameter* (`call_indirect`) is therefore just
// ordinary kernel `App`, checked by `kernel::infer`'s own Pi-application
// rule -- no per-arity axiom needed at all for that generic case (see
// `RELATED_WORK.md` section 11 for the migration away from an earlier,
// opaque-`Clo`-plus-`apply_k`-axiom design). Two different arities stay
// genuinely distinct, definitionally-unequal kernel types on their own,
// with no need to remember "which arity was already postulated" --
// mirroring `compile.rs`'s own `(type $tyK ...)` declarations, one per
// arity actually used at a `call_indirect` site, this part is unaffected
// by whether the underlying closure happens to capture anything, the same
// way `lower_wat.rs`'s own `call_indirect` dispatch doesn't need to know
// either. The one genuine axiom this generic case still needs is
// `ite_clo_ref` (`Int -> Clo_k -> Clo_k -> Clo_k`, once per arity): an
// `If` choosing between two same-arity closures can't be derived from
// `Clo_k` being a real Pi type alone, since `Int` (the condition's own
// type) has no case-eliminator in this kernel.
//
// A combinator's own *body* is never unfolded or denoted here -- it's
// referenced only by postulated symbols. For a *non-capturing* combinator
// this is one `Clo_k`-typed constant (`combinator_value`, for `h` used as
// a bare value) and one `call_h : T_0 -> .. -> T_{k-1} -> Int` (for a
// direct call), each memoized by hash: faithful on both readings, since a
// non-capturing closure really is the same value everywhere it's
// referenced, and calling it really doesn't need anything beyond its own
// definition. For a *capturing* combinator, one fixed value per
// combinator would be dishonest -- the compiled code (`lower_wat.rs`'s
// templates) builds a fresh environment at every creation site, so the same combinator denotes
// differently depending on *where* it's referenced -- so instead:
// `mk_clo_h : Env -> Clo_k` (a function of the environment, not a bare
// constant) and `call_h : Env -> T_0 -> .. -> T_{k-1} -> Int` (the
// environment prepended, mirroring `lower_wat.rs`'s calling convention
// of `$env` as a combinator's first Wasm parameter -- a lambda-lifted
// (`direct_only`) one receives the same values as separate leading
// parameters instead, which this one `Env` argument models equally), where `Env :
// Sort(0)` is postulated once *per capture signature* (which of its
// slots are `Clo_k`-typed, which are `Int` -- `capture_sig`; shared
// across every combinator whose captures happen to match that exact
// signature, the same way `Clo_k` itself is shared by arity, not
// postulated per combinator) with constructor `mk_env : T_0 -> .. ->
// T_{n-1} -> Env`. `build_env_expr` builds the actual `mk_env(v_1,...,
// v_n)` argument fresh at each creation site, from whatever the captured
// values currently are in the *calling* function's own frame -- exactly
// mirroring `lower_wat.rs`'s `push_closure_env` at the proof level.
// Either way -- ordinary `App` against a `Clo_k`-typed parameter, or
// `call_h` applied to its arguments for a directly-named combinator --
// the result faithfully represents "call this closure" on *both*
// readings, identically, symbol for symbol, the same way `denote`'s
// postulated `Int` operators represent an arithmetic primitive without
// either reading being numerically verified. The proof is `refl`, same
// as `prove_pure_expr`'s straight-line argument: nothing here evaluates
// anything concrete, so no `assume_prim_fact`-style grounding is needed.
//
// Scope, honestly: the *main*, top-level term must still be non-recursive
// (`prove_closure_expr`'s own top-level check) -- proving what a
// self-recursive function's *own* body computes is `build_universal`'s
// job, not this fragment's. A *combinator* referenced or called from
// within that non-recursive main term, though, may be self-recursive
// (`Term::Rec`, not just `Term::Abs`) -- see the paragraph below; every
// `If` branch must denote as `Int`, or *both* as `Clo` (via `ite_clo`, see
// its own docs -- reachable both when the `If`'s own result is used as a
// value, e.g. an argument to a closure-typed parameter, and when the
// `If` is a directly-called literal lambda's own top-level body:
// `call_ref`'s postulated return type is no longer a blanket `Int`
// assumption -- `combinator_return_type` classifies it structurally, per
// `Hash`, once, without denoting the callee's body in the usual sense --
// see its own docs); and the whole function's
// own result must denote as `Int`, not directly return a closure value.
// For a capturing combinator specifically, `build_env_expr` requires each
// captured value to resolve *directly* to one of the calling scope's own
// parameters -- but that parameter may itself be `Clo`-typed (e.g.
// capturing a closure-typed loop-carried parameter, or a closure value
// bound earlier in the same scope): `Env`/`mk_env` are keyed by the whole
// capture *signature* (`capture_sig`, `Clo` or `Int` per slot), not just
// a count, so a mixed-type environment gets its own honestly-typed
// postulate rather than being forced through an all-`Int` one.
//
// A captured value that's itself a capture of the *calling* scope --
// `build_read`'s own recursive case, when compiling a function that
// is itself a capturing closure -- has no proof-side counterpart here,
// not because it's deferred, but because it can't arise: `denote_closure`/
// `denote_closure_typed` never enter a registered combinator's own body
// (a call is always postulated opaque), and `compile::peel` always folds
// consecutive `Abs` layers into one combinator before that combinator is
// ever registered, so there is no way for this fragment to encounter one
// combinator's own literal-lambda body containing *another*, separately
// registered one -- every capture list `build_env_expr` is ever asked to
// resolve is relative to the one flat ambient scope currently being
// denoted (the top-level term's own parameters, or `build_universal`'s
// own per-iteration frame), which is exactly what `captures`'s own
// relative indices are computed against in the first place.
//
// A literal lambda applied to *fewer* arguments than its own arity mirrors
// `compile.rs`'s own compile-time desugaring (`register_partial_app`): a
// `Clo`-typed value, `mk_pap_h_k : T_0 -> .. -> T_{k-1} -> Clo`, postulated
// once per `(h, k)` pair (`pap_ref`, memoized the same way `register_partial_app`
// dedups by `(root, supplied)` alone, since the wrapper's own compiled body
// depends only on that shape, not on the actual argument *values*). Unlike a
// capturing combinator's environment, the `k` supplied arguments here are
// ordinary call-site subexpressions -- denoted the normal recursive way, not
// resolved through any `Env`/`build_env_expr`-style machinery -- so this
// piece is structurally simpler than the capturing-closures one above.
// Now covers a *capturing* root too, mirroring `lower_wat.rs`'s
// `Lowering::pap_env`: when `h`'s own body captures anything, `pap_ref`'s
// postulated type takes an extra leading `Env` parameter (the same
// environment-first convention `call_ref` already uses for a direct call),
// and every call site builds that environment via `build_env_expr` and
// prepends it to the wrapper's own supplied arguments -- composing the
// wrapper's own environment with a copy of the root's, exactly the way
// `Lowering::pap_env` composes them at the compiled-code level. Over-application
// (more arguments than arity) stays rejected exactly as before.
//
// A combinator (called or used as a bare value) may itself be
// self-recursive (`Term::Rec`, e.g. a named `let fact = rec f n = .. in
// g fact` or a direct `fact(10)`), not just `Term::Abs`: `register`/
// `call_ref`/`param_types_for` never look inside a combinator's own body
// regardless (a call is always postulated opaque, `combinator_value`/
// `mk_clo_h`/`call_h` alike), so widening every `Term::Abs`-only call/value
// site to also accept `Term::Rec` needed no new proof machinery -- just the
// wider pattern, since `compile::peel`/`compile::free_vars`/
// `compile::infer_closure_arities` were already generic over `is_rec`
// (`build_universal`'s own fragment already relied on that). `pap_ref` now
// covers a self-recursive root too, the same way: `compile::peel`/
// `compile::free_vars`/`param_types_for` were already generic over
// `is_rec`, and `compile.rs`'s `register_partial_app`/`lower_wat.rs`'s
// `emit_pap_wrapper` never special-cased it either (a PAP wrapper only ever forwards a static
// call to its root, indifferent to whether that root's own codegen happens
// to loop) -- `pap_ref`'s own extra `is_rec` check was the only thing left
// standing in the way.

/// Either an `Int`-typed or a `Clo`-typed denotation -- `denote_closure`
/// needs to track which, since an application's arguments and an `If`'s
/// branches (in this fragment) must be `Int`, while a call's *callee* and a
/// bare lambda value must be `Clo`.
pub(super) enum Denoted {
    Int(Expr),
    Clo(Expr),
}
impl Denoted {
    pub(super) fn int(self) -> Option<Expr> {
        match self {
            Denoted::Int(e) => Some(e),
            Denoted::Clo(_) => None,
        }
    }
    pub(super) fn clo(self) -> Option<Expr> {
        match self {
            Denoted::Clo(e) => Some(e),
            Denoted::Int(_) => None,
        }
    }
}

/// `h`'s own parameter types, from `compile::infer_closure_arities`'s
/// classification on `h`'s *own* body/arity (already keyed by absolute
/// `Var` index, the same convention `denote_closure` uses -- see its own
/// docs) -- shared by `prove_closure_expr`'s top-level call and
/// `ClosureCombinators::call_ref`'s per-combinator call signature. Only
/// ever looks up indices `0..arity` (this fragment's own params), so a
/// captured-free-variable entry `infer_closure_arities` might also carry
/// (calling a closure reached that way is compile.rs-only territory,
/// still out of `prove_closure_expr`'s own scope) is never consulted.
/// Works for a self-recursive `h` too (`Term::Rec`, not just `Term::Abs`)
/// -- `infer_closure_arities` already excludes the self-binder from this
/// classification when given `self_idx` (same as `build_universal`'s own
/// call), so a self-recursive combinator's *own* parameters classify the
/// same way a non-recursive one's do.
pub(super) fn param_types_for(store: &TermStore, h: Hash) -> Option<Vec<Option<usize>>> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    let self_idx = is_rec.then_some(arity as u32);
    let found = compile::infer_closure_arities(store, body, arity, self_idx)?;
    // An inconsistently-called `Var` is declined here exactly as an
    // absent one already is -- this proof methodology has no way to
    // classify a value whose arity isn't fixed statically (see
    // `compile::ArityUse`'s own docs).
    Some(
        (0..arity as u32)
            .map(|i| match found.get(&i) {
                Some(compile::ArityUse::Consistent(k)) => Some(*k),
                Some(compile::ArityUse::Inconsistent) | None => None,
            })
            .collect(),
    )
}

/// Which shape an application node (`Term::App` chain) takes -- shared by
/// every closures-aware walker that would otherwise re-derive this same
/// dispatch by hand: `unwind_app_spine`, then match the root as a
/// `Clo`-typed parameter or a literal lambda/named recursive combinator,
/// then (for the latter) compare `args.len()` against the callee's own
/// arity. Pure and side-effect-free (`param_types_for` is the only
/// fallible step, itself already pure), so classifying *before* touching
/// a caller's own `combinators` is always safe.
pub(super) enum AppShape {
    /// `Var(i)` (`root`, its own `Hash`) with `param_types[i] = Some(k)`,
    /// called with exactly `k` arguments.
    ParamCall { root: Hash, k: usize, args: Vec<Hash> },
    /// `root` (a literal lambda or named self-recursive combinator)
    /// applied to fewer arguments than its own arity.
    LitLambdaPartial { root: Hash, args: Vec<Hash>, callee_param_types: Vec<Option<usize>> },
    /// `root` applied to exactly its own arity.
    LitLambdaExact { root: Hash, args: Vec<Hash>, callee_param_types: Vec<Option<usize>> },
    /// `root` applied to more arguments than its own arity -- `args` holds
    /// the *whole* list; a consumer wanting just the saturated prefix or
    /// the extra suffix slices it at `callee_param_types.len()`.
    LitLambdaOver { root: Hash, args: Vec<Hash>, callee_param_types: Vec<Option<usize>> },
}

/// Refines an application-shaped [`Shape`] (from `compile::classify`, the
/// same classification `build_node` dispatches on) with what the
/// closures fragment needs to know: whether a variable callee is a
/// `Clo`-typed parameter called at its own arity, and a literal callee's
/// own parameter types. `None` for any other shape.
pub(super) fn app_shape(store: &TermStore, shape: Shape, param_types: &[Option<usize>]) -> Option<AppShape> {
    match shape {
        Shape::VarCall { root, var, args } => {
            let k = (*param_types.get(var as usize)?)?;
            (args.len() == k).then_some(AppShape::ParamCall { root, k, args })
        }
        Shape::CombinatorCall { root, arity, args } => {
            let callee_param_types = param_types_for(store, root)?;
            Some(match args.len().cmp(&arity) {
                std::cmp::Ordering::Less => AppShape::LitLambdaPartial { root, args, callee_param_types },
                std::cmp::Ordering::Equal => AppShape::LitLambdaExact { root, args, callee_param_types },
                std::cmp::Ordering::Greater => AppShape::LitLambdaOver { root, args, callee_param_types },
            })
        }
        _ => None,
    }
}

/// Structurally determines whether `h`'s own saturated call denotes an
/// `Int` (`false`) or a further `Clo` (`true`) -- a per-`Hash`, purely
/// syntactic property of `h`'s own body, needed for a directly-called
/// literal lambda whose saturated result is itself treated as a `Clo`
/// value (over-application, or passing a direct call's result where a
/// `Clo` is expected -- see `ClosureCombinators::call_ref`'s own use of
/// this). `None` for anything this doesn't confidently recognize --
/// callers fall back to assuming `Int`, `call_ref`'s own historical
/// default, which stays sound for every shape this doesn't classify (a
/// term that's genuinely `Clo`-typed but unrecognized here just misses
/// out on the widening, the same "sound, not complete" tradeoff this
/// whole fragment already makes everywhere else).
///
/// Well-founded, so no memoization is needed: a self-call (`Var(self_idx)`)
/// is always `Int` by this whole fragment's own convention, so recursing
/// into `h`'s own body never needs `h`'s *own* classification to classify
/// itself; calling a *different* literal lambda recurses into *that*
/// lambda's own body instead, a distinct, already-fully-built term
/// (hash-consing only ever lets a term reference an *already-existing*
/// sub-hash, so the "calls" relation between distinct combinators is a
/// strict partial order matching construction order -- it can't cycle
/// back to `h`). A captured free variable's own type never needs
/// resolving either: calling *any* closure-typed value -- a parameter, a
/// capture, or (now) another directly-called combinator's own saturated
/// result -- always denotes `Int` (a saturated call against a `Clo_k`-
/// typed value is ordinary `App`, whose codomain is `Int` by `Clo_k`'s
/// own construction -- the same convention `denote_closure`'s own
/// `Term::Var(i)` case already relies on), so this only ever needs `h`'s
/// *own* declared parameters' types (`param_types_for`), never a
/// capture's.
pub(super) fn combinator_return_type(store: &TermStore, h: Hash) -> Option<Option<usize>> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    let self_idx = is_rec.then_some(arity as u32);
    let param_types = param_types_for(store, h)?;
    return_type_of(store, body, arity, self_idx, &param_types)
}

/// The extra arity a `k`-of-`arity` partial application of `root`
/// contributes *beyond* its own `arity - k` still-undeclared parameters,
/// once every remaining parameter is finally supplied: `0` when `root`'s
/// own saturated call denotes `Int` (the common case, and also this
/// fragment's historical default when `combinator_return_type` can't
/// confidently classify `root` at all -- consistent with every other
/// structural classifier here, "undetermined" conservatively means
/// "assume no widening", not "assume the widening is definitely there"),
/// `m` when it denotes a further `Clo_m`. Folding this into a flat
/// "remaining arity" figure is sound, not approximate: `Clo_j`/`Clo_m`
/// are both literal, associative Pi-type chains
/// (`ClosurePostulates::clo_ty`/`curried_int_ty`), so `Int^(arity-k) ->
/// Clo_m` is *definitionally the same term*, arrow for arrow, as
/// `Clo_{(arity-k)+m}` -- not merely isomorphic to it -- whenever every
/// one of those `arity - k` remaining parameters is itself plain `Int`
/// (never itself `Clo`-typed; every call site below already restricts to
/// that case independently, e.g. `clo_eq_ref_pap`'s own `g_param_types`
/// check).
///
/// Missing before this was added: every one of this function's own call
/// sites silently assumed a `k`-of-`arity` partial application's
/// remaining shape is always `Clo_{arity-k}`, with no extra arity ever
/// folded in -- correct only when `root`'s own saturated call happens to
/// return `Int`. When it instead returns a further `Clo_m` (e.g. `root =
/// \p a. if a==0 then id else add_something`, whose own saturated result
/// is itself a one-argument closure), the old formula built a
/// `pap_ref` postulate -- and every downstream structural classification
/// derived from it -- claiming the partial application's remaining shape
/// was `Clo_{arity-k}` when the honest type is `Clo_{(arity-k)+m}`. Since
/// `Clo_k` is a literal kernel Pi type (not an opaque postulate), the
/// kernel had no way to catch the mismatch on its own: `prove_closure_expr`
/// built a `refl`-based proof the kernel happily checked, `jit.rs` marked
/// the term `is_kernel_verified`, and the compiled code -- genuinely
/// dispatching one argument short of what the runtime value needed --
/// returned whatever raw bits its own extra `call_indirect` produced
/// (garbage, not a trap) at an input outside `verify()`'s own finite
/// sample battery.
pub(super) fn pap_extra_arity(store: &TermStore, root: Hash) -> usize {
    combinator_return_type(store, root).flatten().unwrap_or(0)
}

/// `combinator_return_type`'s own recursive walk over one combinator's
/// body (`arity`/`self_idx`/`param_types` all describe *that* combinator,
/// unchanged across the whole walk -- only `h` itself moves, the same
/// convention `find_self_calls`'s own recursion uses) -- also reused
/// directly (with `self_idx` possibly `None`, and `arity`/`param_types`
/// describing whatever ambient scope `h` sits in) by `denote_closure`/
/// `denote_closure_typed`/`denote_with_placeholders`'s own nested-`If`
/// case, to learn *which* arity's `ite_clo_ref`/`clo_ty` two `Clo`-typed
/// branches share -- a fully general "what does this expression denote"
/// structural classifier, not just a combinator-body-specific one; every
/// shape it recognizes here is kept in exact lockstep with the shapes
/// those functions' own `Denoted::Clo`-producing cases recognize, so the
/// two never disagree when both succeed. `None` for anything this doesn't
/// confidently recognize -- callers fall back to assuming `Int` (a
/// combinator's own return type) or rejecting outright (a nested `If`'s
/// own branch arity, where guessing wrong would be unsound), the same
/// "sound, not complete" tradeoff this whole fragment already makes
/// everywhere else. The outer `Option` is "undetermined"; the inner one is
/// the actual type, `None` for `Int`, `Some(k)` for `Clo_k`.
pub(super) fn return_type_of(store: &TermStore, h: Hash, arity: usize, self_idx: Option<u32>, param_types: &[Option<usize>]) -> Option<Option<usize>> {
    match compile::classify(store, h, arity, self_idx) {
        Shape::SelfCall(_) => Some(None), // a self-call's own result is always Int
        // Calling a parameter, a capture, or (recursively) another
        // directly-called combinator's own result: always Int, since a
        // saturated call against a `Clo_k`-typed value is ordinary `App`
        // whose codomain is `Int` -- the same over-application-dispatch
        // convention.
        Shape::VarCall { .. } => Some(None),
        Shape::CombinatorCall { root, arity: callee_arity, args } => {
            param_types_for(store, root)?;
            match args.len().cmp(&callee_arity) {
                std::cmp::Ordering::Equal => combinator_return_type(store, root),
                // A partial-application value is always Clo, of the
                // *remaining* arity (the wrapper still expects
                // `callee_arity - args.len()` more arguments) plus whatever
                // extra arity `root`'s own saturated call itself
                // contributes -- see `pap_extra_arity`'s own docs for why
                // folding it in this way is exact, not approximate.
                std::cmp::Ordering::Less => Some(Some(callee_arity - args.len() + pap_extra_arity(store, root))),
                std::cmp::Ordering::Greater => Some(None), // over-application's own dispatch is always Int
            }
        }
        Shape::OtherCall => None,
        // A bare parameter, read as a value (not called) -- its own
        // declared type; out of range (a bare captured free variable, or
        // this combinator's own self-reference as a plain value, still
        // unsupported) is undetermined, not an error.
        Shape::Var(i) => {
            let i = i as usize;
            if i < arity { Some(*param_types.get(i)?) } else { None }
        }
        Shape::Lit(_) | Shape::Prim(..) => Some(None),
        Shape::If(_, t, e) => {
            let dt = return_type_of(store, t, arity, self_idx, param_types)?;
            let de = return_type_of(store, e, arity, self_idx, param_types)?;
            (dt == de).then_some(dt)
        }
        // A fresh closure value, of its own peeled arity.
        Shape::Combinator { .. } => {
            let (own_arity, _, _) = compile::peel(store, h)?;
            Some(Some(own_arity))
        }
    }
}

/// An argument's denotation, for a callee parameter of type `want` (`None`
/// for `Int`, `Some(k)` for `Clo_k`); `actual` computes the argument's own
/// `return_type_of`, only when `want` is a `Clo`. A `Clo` argument must have exactly the parameter's
/// arity: `\g. g 1` applied to `\x. \y. x + y` passes a `Clo_2` where
/// `g : Clo_1`, and composing that would be ill-typed in the kernel.
pub(super) fn arg_denotation(d: Denoted, want: Option<usize>, actual: impl FnOnce() -> Option<Option<usize>>) -> Option<Expr> {
    match want {
        Some(k) if actual() == Some(Some(k)) => d.clo(),
        Some(_) => None,
        None => d.int(),
    }
}

/// Extends `ArithPostulates` with postulated closure-value support -- see
/// the section docs above.
#[derive(Clone)]
pub(super) struct ClosurePostulates {
    pub(super) arith: ArithPostulates,
    pub(super) combinator_value_pos: HashMap<Hash, usize>,
    pub(super) combinator_call_pos: HashMap<Hash, usize>,
    pub(super) env_ty_pos: HashMap<Vec<Option<usize>>, usize>,
    pub(super) mk_env_pos: HashMap<Vec<Option<usize>>, usize>,
    pub(super) mk_clo_pos: HashMap<Hash, usize>,
    pub(super) pap_pos: HashMap<(Hash, usize), usize>,
    pub(super) ite_clo_pos: HashMap<usize, usize>,
    /// `call_eq_ref`'s own memoization -- see its docs.
    pub(super) call_eq_pos: HashMap<Hash, usize>,
    /// `clo_eq_ref`'s own memoization -- see its docs. Keeps the matched
    /// `ClosureRhsShape` alongside the axiom's own position so a memo hit
    /// doesn't need to re-classify `h`'s own body.
    pub(super) clo_eq_pos: HashMap<Hash, (usize, ClosureRhsShape)>,
    /// `ite_clo_eq_ref`'s own memoization -- see its docs. Keyed by the
    /// concrete condition value, not a collapsed boolean (see its docs).
    pub(super) ite_clo_eq_pos: HashMap<(i64, usize), usize>,
    /// `apply_clo_eq_ref`'s own memoization -- see its docs.
    pub(super) apply_clo_eq_pos: HashMap<Hash, usize>,
    /// `apply_pap_eq_ref`'s own memoization -- see its docs.
    pub(super) apply_pap_eq_pos: HashMap<(Hash, usize), usize>,
}

/// Lets code holding a `&(mut) ClosurePostulates` -- `build_universal`'s own
/// closure-aware pipeline, primarily -- call every `ArithPostulates` method
/// (`int_ty`, `lit_ref`, `p.push`, ...) directly, without a manual `.arith`
/// hop at each use. The one place this bites: *moving* a field out of the
/// inner `ArithPostulates` (e.g. `UniversalTailProof`'s own `globals:
/// scaffold.combinators.cp.arith.p.globals`) can't go through a `Deref` (it only
/// ever hands back a reference) and still needs the explicit `.arith` hop
/// -- everywhere else (methods, borrows) this is transparent.
impl std::ops::Deref for ClosurePostulates {
    type Target = ArithPostulates;
    fn deref(&self) -> &ArithPostulates {
        &self.arith
    }
}
impl std::ops::DerefMut for ClosurePostulates {
    fn deref_mut(&mut self) -> &mut ArithPostulates {
        &mut self.arith
    }
}

impl ClosurePostulates {
    pub(super) fn new() -> Self {
        let arith = ArithPostulates::new();
        ClosurePostulates {
            arith,
            combinator_value_pos: HashMap::new(),
            combinator_call_pos: HashMap::new(),
            env_ty_pos: HashMap::new(),
            mk_env_pos: HashMap::new(),
            mk_clo_pos: HashMap::new(),
            pap_pos: HashMap::new(),
            ite_clo_pos: HashMap::new(),
            call_eq_pos: HashMap::new(),
            clo_eq_pos: HashMap::new(),
            ite_clo_eq_pos: HashMap::new(),
            apply_clo_eq_pos: HashMap::new(),
            apply_pap_eq_pos: HashMap::new(),
        }
    }

    /// `Clo_arity := Int -> .. -> Int` (`arity` copies) -- the literal
    /// curried arrow type, *not* postulated (see `RELATED_WORK.md` section
    /// 11 for the investigation this answers): every consumer below only
    /// ever needs "the callable shape with `arity` `Int` parameters and an
    /// `Int` result" (every argument/result stays uniformly `Int`
    /// regardless of what the callee's own body does with them, matching
    /// `lower_wat.rs`'s own untyped `call_indirect` dispatch), and a
    /// real Pi type already gives that for free -- no opaque `Sort(0)`
    /// axiom needed at all. Two different arities still stay genuinely
    /// distinct, definitionally-unequal kernel types (the fix for the
    /// "arity-blind `Clo`" gap `TYPES.md` section 7 describes): `Int ->
    /// Int` and `Int -> Int -> Int` are already structurally distinct
    /// under `kernel::check`'s own Pi-formation rules, with no reliance on
    /// remembering "which arity was already postulated" the way the old
    /// opaque-tag scheme needed. Pure with respect to its own return
    /// value -- safe to call any number of times, no staleness risk at
    /// all (contrast the old memoized version's own careful
    /// re-resolve-after-push dance).
    pub(super) fn clo_ty(&mut self, arity: usize) -> Expr {
        self.curried_int_ty(arity)
    }

    /// The literal `Int -> .. -> Int` (`arity` copies) type -- `clo_ty`'s
    /// own core, factored out so `ite_clo_ref` can use this same shape for
    /// its own domain/codomain without calling back into `clo_ty` itself.
    pub(super) fn curried_int_ty(&self, arity: usize) -> Expr {
        let int_ty = self.arith.int_ty();
        let mut ty = int_ty.clone();
        for _ in 0..arity {
            ty = kernel::arrow(int_ty.clone(), ty);
        }
        ty
    }

    /// `ite_clo_arity : Int -> Clo_arity -> Clo_arity -> Clo_arity`,
    /// postulated once per distinct `arity` (lazily, unlike
    /// `ArithPostulates::ite_ref`'s eager one -- a term never choosing
    /// between two closures of that particular arity shouldn't pay for
    /// this postulate) -- the `Clo_arity`-valued counterpart to `ite_ref`,
    /// needed for an `If` that chooses between two same-arity closures
    /// rather than two `Int`s (e.g. `if c then (\y. x+y) else (\y. x-y)`).
    /// The condition itself stays `Int` either way -- only the two
    /// branches (and the result) differ. Genuinely opaque and not
    /// derivable, unlike `Clo_arity` itself: its condition is `Int`, and
    /// `Int` has no recursor in this kernel (deliberately -- it's an
    /// open-ended arithmetic domain, grounded only per concrete value, see
    /// `ArithPostulates::assume_prim_fact`/`assume_ite_fact`, never given a
    /// case-elimination principle), so there's no way to build this from
    /// anything already postulated (see `RELATED_WORK.md` section 11's own
    /// correction). Called directly by whichever site needs it.
    pub(super) fn ite_clo_ref(&mut self, arity: usize) -> Expr {
        if let Some(&pos) = self.ite_clo_pos.get(&arity) {
            return self.arith.p.get(pos);
        }
        let clo_ty = self.curried_int_ty(arity);
        let ite_ty = kernel::arrow(self.arith.int_ty(), kernel::arrow(clo_ty.clone(), kernel::arrow(clo_ty.clone(), clo_ty)));
        let pos = self.arith.p.push(ite_ty);
        self.ite_clo_pos.insert(arity, pos);
        self.arith.p.get(pos)
    }

    /// A fresh `Clo_arity`-typed constant for combinator `h` (own arity
    /// `arity`), memoized by hash -- for a *non-capturing* combinator used
    /// as a bare value (an argument, a branch result, ...), mirroring
    /// `compile.rs`'s "its value is just its table index" reading. A
    /// *capturing* combinator's own value needs `mk_clo_ref` instead --
    /// see its docs for why one fixed constant isn't an honest model there.
    pub(super) fn combinator_value(&mut self, h: Hash, arity: usize) -> Expr {
        if let Some(&pos) = self.combinator_value_pos.get(&h) {
            return self.arith.p.get(pos);
        }
        let clo_ty = self.clo_ty(arity);
        let pos = self.arith.p.push(clo_ty);
        self.combinator_value_pos.insert(h, pos);
        self.arith.p.get(pos)
    }

    /// `Env_sig : Sort(0)`, postulated once per distinct capture
    /// *signature* (never per-combinator) -- an opaque bundle of
    /// `sig.len()` captured values, `Clo_k`-typed wherever `sig[i]` is
    /// `Some(k)`, `Int`-typed wherever it's `None` -- mirroring
    /// `compile.rs`'s own uniform, combinator-agnostic environment-slot
    /// layout at the proof level (every slot is just an `i64` there,
    /// whatever it holds). Shared across every combinator whose captures
    /// happen to match this exact signature, the same way `Clo_k` itself
    /// (`ClosurePostulates::clo_ty`) is shared across every closure of
    /// arity `k` regardless of which combinator it turns out to be -- two
    /// combinators that both
    /// capture, say, three plain `Int`s still share one `Env` (the common
    /// case, keyed by an all-`None` signature exactly as it used to be
    /// keyed by the count `3` alone); only a genuinely mixed, or
    /// genuinely differently-sized-closure, signature gets its own.
    pub(super) fn env_ty(&mut self, sig: &[Option<usize>]) -> Expr {
        if let Some(&pos) = self.env_ty_pos.get(sig) {
            return self.arith.p.get(pos);
        }
        let pos = self.arith.p.push(kernel::sort(0));
        self.env_ty_pos.insert(sig.to_vec(), pos);
        self.arith.p.get(pos)
    }

    /// `mk_env_sig : T_0 -> .. -> T_{n-1} -> Env_sig` (`T_i` = `Clo_k` if
    /// `sig[i] == Some(k)` else `Int`) -- `env_ty(sig)`'s constructor,
    /// postulated once per signature.
    pub(super) fn mk_env_ref(&mut self, sig: &[Option<usize>]) -> Expr {
        if let Some(&pos) = self.mk_env_pos.get(sig) {
            return self.arith.p.get(pos);
        }
        // `env_ty(sig)` may lazily push its own postulate on first use;
        // `clo_ty` is pure and never pushes.
        let env_ty = self.env_ty(sig);
        let doms: Vec<Expr> = sig
            .iter()
            .map(|slot| match slot {
                Some(k) => self.clo_ty(*k),
                None => self.arith.int_ty(),
            })
            .collect();
        let mut ty = env_ty.clone();
        // Fold from the *last* capture outward, so the final iteration
        // (sig[0]) ends up as the outermost/first-applied parameter,
        // matching `apply_n`'s left-to-right application order (the same
        // convention `call_ref`'s own loop documents).
        for dom in doms.iter().rev() {
            ty = kernel::arrow(dom.clone(), ty);
        }
        let pos = self.arith.p.push(ty);
        self.mk_env_pos.insert(sig.to_vec(), pos);
        self.arith.p.get(pos)
    }

    /// `mk_clo_h : Env_sig -> Clo_arity`, for a *capturing* combinator `h`
    /// (own arity `arity`, own capture signature `sig`) used as a bare
    /// value -- the capturing counterpart to `combinator_value`, one
    /// postulated constant (function, here) per combinator just like it,
    /// but correctly varying with `h`'s own environment (built fresh from
    /// the *actual* captured values at each creation site by
    /// `build_env_expr`, not baked into `mk_clo_h` itself) instead of
    /// being one fixed value wherever `h` is referenced -- an honest
    /// reading of "a different runtime environment pointer at every
    /// creation site" the way `combinator_value`'s single constant only
    /// ever was for a non-capturing closure.
    pub(super) fn mk_clo_ref(&mut self, h: Hash, sig: &[Option<usize>], arity: usize) -> Expr {
        if let Some(&pos) = self.mk_clo_pos.get(&h) {
            return self.arith.p.get(pos);
        }
        // `env_ty(sig)` may lazily push its own postulate on first use;
        // `clo_ty` is pure and never pushes.
        let env_ty = self.env_ty(sig);
        let clo_ty = self.clo_ty(arity);
        let ty = kernel::arrow(env_ty.clone(), clo_ty);
        let pos = self.arith.p.push(ty);
        self.mk_clo_pos.insert(h, pos);
        self.arith.p.get(pos)
    }
}

/// Registers combinators on demand -- unlike `compile.rs`'s own
/// `Combinators`, there's no fixpoint queue to drain: a combinator's body
/// is never denoted here (see the section docs above), so registering one
/// never discovers more work.
#[derive(Clone)]
pub(super) struct ClosureCombinators<'a> {
    pub(super) store: &'a TermStore,
    pub(super) cp: ClosurePostulates,
}

/// Same rationale as `ClosurePostulates`'s own `Deref`/`DerefMut` (see its
/// docs) -- lets code holding a `&(mut) ClosureCombinators`
/// (`build_universal`'s own pipeline, once it needs to create a closure
/// value itself, not just call one through a parameter) call every
/// `ArithPostulates`/`ClosurePostulates` method directly, chained through
/// both layers.
impl<'a> std::ops::Deref for ClosureCombinators<'a> {
    type Target = ClosurePostulates;
    fn deref(&self) -> &ClosurePostulates {
        &self.cp
    }
}
impl<'a> std::ops::DerefMut for ClosureCombinators<'a> {
    fn deref_mut(&mut self) -> &mut ClosurePostulates {
        &mut self.cp
    }
}

impl<'a> ClosureCombinators<'a> {
    pub(super) fn new(store: &'a TermStore) -> Self {
        ClosureCombinators { store, cp: ClosurePostulates::new() }
    }

    /// The postulated `Clo`-typed value for combinator `h` used as a bare
    /// value: `combinator_value(h)` (one fixed constant) if `h` doesn't
    /// capture anything, or `mk_clo_ref(h, sig)` (a function from
    /// environment to `Clo`, applied to its own environment by
    /// `denote_closure` -- this only returns the bare, unapplied
    /// constructor) if it does. `captures` is `h`'s own relative capture
    /// indices (`compile::free_vars`, computed once by the caller and
    /// passed in rather than re-derived here, since the caller needs it
    /// again anyway to build the actual environment via
    /// `build_env_expr`); `caller_param_types` is the *calling* scope's
    /// own `param_types`, needed to resolve each capture's `Clo`/`Int`
    /// signature (`capture_sig`) -- a captured value may itself be
    /// `Clo`-typed (e.g. capturing a closure-typed loop-carried parameter),
    /// which `Env`/`mk_env` now represent directly rather than assuming
    /// every capture is `Int`. `None` for a zero-arity `h` only -- a
    /// self-recursive `h` (`Term::Rec`) is fine here, the same opaque
    /// constant/function either way, since a call is never denoted by
    /// looking inside `h`'s own body regardless of whether it recurses.
    pub(super) fn register(&mut self, h: Hash, captures: &[u32], caller_param_types: &[Option<usize>]) -> Option<Expr> {
        let (arity, _, _) = compile::peel(self.store, h)?;
        if arity == 0 {
            return None;
        }
        if captures.is_empty() {
            Some(self.cp.combinator_value(h, arity))
        } else {
            let sig = capture_sig(captures, caller_param_types)?;
            Some(self.cp.mk_clo_ref(h, &sig, arity))
        }
    }

    /// A postulated function for *directly calling* combinator `h` (a
    /// static Wasm `call`, not dispatched through any `Clo` value at all
    /// -- no leading `Clo` argument here), memoized by hash:
    /// `T_0 -> T_1 -> .. -> T_{k-1} -> R` if `h`
    /// doesn't capture anything, or `Env -> T_0 -> .. -> T_{k-1} -> R`
    /// (`n` = `captures.len()`) if it does -- the environment, when
    /// present, is always the *first* parameter, ahead of `h`'s own
    /// call arguments, mirroring `lower_wat.rs`'s calling convention
    /// (a combinator reachable through the table takes `$env` as its
    /// first Wasm parameter, whether or not its own body reads from it;
    /// a lambda-lifted one takes the same values as separate leading
    /// parameters). Each `T_j` (`j` in
    /// application order, i.e. `T_0` is the *first*-applied argument's
    /// type) is `Clo_k` (some arity `k`) or `Int` matching `h`'s own
    /// `param_types` at that position -- this is what lets a combinator
    /// like `twice` (`Clo_1 -> Int -> Int`, since its own `f` parameter is
    /// itself closure-typed) be called with a mix of closure and
    /// plain-`Int` arguments, which a single uniform signature per arity
    /// couldn't express. `R` itself
    /// is `Clo` when `combinator_return_type(h)` says so (over-application
    /// dispatches on it, or a caller elsewhere treats a directly-called
    /// combinator's own result as a value -- see either use site), `Int`
    /// otherwise, including whenever the classifier can't tell -- the
    /// same conservative default it's always had, now just sometimes
    /// overridden by a real answer instead of universally assumed.
    /// `captures`, as in `register`, is computed once by the caller and
    /// passed in; `caller_param_types` (the *calling* scope's own
    /// `param_types`, distinct from `h`'s own `param_types` used for
    /// `T_0..T_{k-1}` above) resolves each capture's own `Clo`/`Int`
    /// signature the same way `register` does.
    pub(super) fn call_ref(&mut self, h: Hash, captures: &[u32], caller_param_types: &[Option<usize>]) -> Option<Expr> {
        if let Some(&pos) = self.cp.combinator_call_pos.get(&h) {
            return Some(self.cp.arith.p.get(pos));
        }
        let param_types = param_types_for(self.store, h)?;
        let return_ty = combinator_return_type(self.store, h).unwrap_or(None);
        let sig = capture_sig(captures, caller_param_types)?;
        // `env_ty` may lazily push its own postulate on first use; the
        // return type's and each parameter's `clo_ty` is pure and never
        // pushes.
        let env_ty = (!sig.is_empty()).then(|| self.cp.env_ty(&sig));
        let ret = match return_ty {
            Some(k) => self.cp.clo_ty(k),
            None => self.cp.arith.int_ty(),
        };
        let doms: Vec<Expr> = param_types
            .iter()
            .map(|pt| match pt {
                Some(k) => self.cp.clo_ty(*k),
                None => self.cp.arith.int_ty(),
            })
            .collect();
        let mut ty = ret.clone();
        // Var(0) is last-applied (innermost -- wrap it first, so the
        // final iteration, Var(arity-1) = first-applied, ends up
        // outermost, matching apply_n's left-to-right application order).
        for dom in &doms {
            ty = kernel::arrow(dom.clone(), ty);
        }
        if let Some(env_ty) = env_ty {
            ty = kernel::arrow(env_ty.clone(), ty);
        }
        let pos = self.cp.arith.p.push(ty);
        self.cp.combinator_call_pos.insert(h, pos);
        Some(self.cp.arith.p.get(pos))
    }

    /// A postulated `Clo`-typed value for the `compile.rs`-synthesized
    /// wrapper combinator that partially applies `h` to its first `k`
    /// arguments (`register_partial_app`'s own `(root,
    /// supplied)` shape): `T_0 -> .. -> T_{k-1} -> Clo`, memoized by
    /// `(h, k)` -- like `register_partial_app` itself, the wrapper's
    /// compiled body only depends on the *shape* `(h, k)`, never on the
    /// actual supplied argument values, so those are denoted normally by
    /// the caller and applied here, not folded into the postulate's own
    /// identity the way a captured value is folded into `Env`.
    ///
    /// Each `T_j` is `h`'s own `param_types` at the position `args[j]`
    /// (application order) actually fills: for a `k`-of-`arity` partial
    /// application, that's the *first* `k`-applied positions, i.e. the
    /// **last** `k` entries of `param_types` (`param_types[arity-k..]`,
    /// not the first `k` -- `param_types[i]` describes `Var(i)`, and
    /// `Var(arity-1)` is first-applied, `Var(arity-k)` is `k`-th-applied,
    /// matching `call_ref`'s own `Var(0)`-innermost/`Var(arity-1)`-outermost
    /// convention and this function's own ascending iteration order below).
    ///
    /// If `h` itself captures (`lower_wat.rs`'s `Lowering::pap_env` composes
    /// the wrapper's own environment with a copy of `h`'s -- see its own
    /// docs), `mk_pap_h_k` takes `h`'s own `Env` first, ahead of the `k`
    /// supplied arguments, mirroring `call_h`'s own environment-first
    /// convention: `Env -> T_0 -> .. -> T_{k-1} -> Clo`. `caller_param_types`
    /// (the *calling* scope's own `param_types`) resolves `h`'s own
    /// captures' `Clo`/`Int` signature, the same way `register`/`call_ref`
    /// do. `env_ty` below may lazily push a fresh postulate on its own
    /// first use; `clo_ty` is pure and never pushes.
    ///
    /// `None` for a zero-`k` or over-`k` (`k >= arity`) root -- `h` may
    /// itself be self-recursive (`Term::Rec`, not just `Term::Abs`):
    /// `compile::peel`/`compile::free_vars`/`param_types_for` are all
    /// already generic over that (a call is always postulated opaque
    /// regardless), and `compile.rs`'s `register_partial_app`/
    /// `lower_wat.rs`'s `emit_pap_wrapper` never special-cased it either -- a static
    /// forwarding call to `root`'s own table entry, indifferent to
    /// whether that entry's *own* codegen happens to loop.
    pub(super) fn pap_ref(&mut self, h: Hash, k: usize, caller_param_types: &[Option<usize>]) -> Option<Expr> {
        if let Some(&pos) = self.cp.pap_pos.get(&(h, k)) {
            return Some(self.cp.arith.p.get(pos));
        }
        let (arity, body, is_rec) = compile::peel(self.store, h)?;
        if k == 0 || k >= arity {
            return None;
        }
        let captures = compile::free_vars(self.store, body, arity, is_rec);
        let param_types = param_types_for(self.store, h)?;
        let sig = capture_sig(&captures, caller_param_types)?;
        // `env_ty` may lazily push its own postulate; every `clo_ty`
        // below is pure and never pushes.
        let env_ty = (!sig.is_empty()).then(|| self.cp.env_ty(&sig));
        // `ret` -- the type of the *value* this wrapper produces once its
        // own `k` supplied arguments are given -- is `Clo_{arity-k}` only
        // when `h`'s own saturated call denotes `Int`; when it instead
        // denotes a further `Clo_m`, the produced value still needs
        // `arity - k` more plain arguments *and then* whatever `Clo_m`
        // itself still needs, which is the same value as `Clo_{(arity-k)+m}`
        // (`pap_extra_arity`'s own docs explain why this fold is exact,
        // not approximate). Previously always `clo_ty(arity - k)`,
        // silently assuming `Int` regardless of what `h` itself returns --
        // see `pap_extra_arity`'s own docs for the bug this fixes.
        let ret = self.cp.clo_ty(arity - k + pap_extra_arity(self.store, h));
        let doms: Vec<Expr> = param_types[arity - k..]
            .iter()
            .map(|pt| match pt {
                Some(j) => self.cp.clo_ty(*j),
                None => self.cp.arith.int_ty(),
            })
            .collect();
        let mut ty = ret.clone();
        for dom in &doms {
            ty = kernel::arrow(dom.clone(), ty);
        }
        if let Some(env_ty) = env_ty {
            ty = kernel::arrow(env_ty.clone(), ty);
        }
        let pos = self.cp.arith.p.push(ty);
        self.cp.pap_pos.insert((h, k), pos);
        Some(self.cp.arith.p.get(pos))
    }

    /// A computation-rule axiom for `call_ref(h)`: `call_ref`'s own
    /// postulate is deliberately opaque (see this struct's own docs -- a
    /// combinator's body is never denoted for the universal/type-level
    /// proof), which is fine for that proof's own purely-structural
    /// guarantee, but a *concrete instance* proof (`eval_and_prove`) needs
    /// to claim an actual value for a call, not just its type, and there's
    /// no honest way to get one out of an opaque postulate directly. This
    /// mirrors `build_universal`'s own `loop_val_leaf_eq_i` one level down:
    /// a postulated function has no built-in reduction rule, so its
    /// computation rule is postulated directly as a propositional
    /// (`Id`-typed) axiom -- sourced from `h`'s own *real* body via
    /// `denote`, not asserted per call site, so it can't be circular the
    /// way a per-instance "trust the interpreter" axiom would be: nothing
    /// else in this file ever asserts an equation about `call_ref(h)`, so
    /// this axiom is the *only* thing that gives it defined behavior,
    /// exactly the way `assume_prim_fact` is the only thing that defines
    /// what `op_ref` computes on given literals.
    ///
    /// Restricted to `h`'s own body being `Var`/`Lit`/`Prim`/`If` only (no
    /// further `Abs`/`App`) and every one of `h`'s own params being
    /// `Int`-typed, `None` otherwise (a genuine restriction, not an error):
    /// both are required for the axiom's own RHS to be buildable via
    /// `denote` at all (which has no `Abs`/`App` support), and widening
    /// either would mean *this* axiom's own construction might itself need
    /// to register further combinators -- reintroducing the fixpoint-queue
    /// machinery this module was deliberately built without (see its own
    /// docs).
    ///
    /// `h`'s own captures are always resolved, by every caller of this
    /// method, against an outer frame that's entirely `Int`-typed (the only
    /// caller, `eval_and_prove`, only ever reaches this from
    /// `instance_from_scaffold`'s own all-`Int`-params precondition) -- so
    /// `h`'s own capture signature is always all-`None` here, computed
    /// directly rather than looked up against any one real calling scope:
    /// this axiom is universal, built once per `Hash`, reused at every call
    /// site, not tied to a specific one.
    pub(super) fn call_eq_ref(&mut self, h: Hash) -> Option<Expr> {
        if let Some(&pos) = self.cp.call_eq_pos.get(&h) {
            return Some(self.cp.arith.p.get(pos));
        }
        let (arity, body, is_rec) = compile::peel(self.store, h)?;
        if is_rec {
            return None; // a literal lambda encountered mid-expression is never self-recursive
        }
        let param_types = param_types_for(self.store, h)?;
        if param_types.iter().any(Option::is_some) {
            return None;
        }
        if combinator_return_type(self.store, h) != Some(None) {
            return None;
        }
        let captures = compile::free_vars(self.store, body, arity, is_rec);
        let n_captures = captures.len();
        // A dummy all-`None` caller scope, long enough to cover every
        // relative index `captures` mentions -- `capture_sig`/`call_ref`
        // only ever read it at those positions, and every one of them is
        // `None` regardless of which real outer scope this axiom later
        // gets used from (see this method's own docs).
        let dummy_caller_param_types: Vec<Option<usize>> = vec![None; captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let sig = capture_sig(&captures, &dummy_caller_param_types)?;

        // `h`'s own body's literals are never collected by any existing
        // pass (a combinator's body is always opaque to
        // `collect_literals`/`collect_literals_closure`, by the same
        // design that keeps it opaque to `denote_closure` -- see their own
        // docs) -- collected here, explicitly, before `denote` below needs
        // to read any of them back via `lit_ref`.
        let mut lits = Vec::new();
        if !collect_literals(self.store, body, arity, None, None, &mut lits) {
            return None;
        }
        for lit_n in lits {
            self.cp.arith.lit(lit_n);
        }

        // Resolved (and, transitively, `mk_env_ref`/`clo_ty` etc. pushed as
        // needed) before the quantified construction below.
        let call_fn = self.call_ref(h, &captures, &dummy_caller_param_types)?;

        // Quantify `n_captures + arity` fresh `Int` postulates -- captures
        // first, then `h`'s own params, an arbitrary but fixed order (only
        // the *values* pulled out of `pp` below need to match this).
        let quant_types = vec![None; n_captures + arity];
        let store = self.store;
        let ty = params_and_close_typed(self, &quant_types, kernel::Binder::Pi, |combinators, pp| {
            let (cs, ps) = pp.split_at(n_captures);
            let call_fn_here = call_fn.clone();

            // LHS: `call_ref(h)` applied to `(env?, p_{arity-1}, ..,
            // p_0)` -- *descending* `Var` order, matching `call_ref`'s own
            // convention (`Var(0)` is last-applied, `Var(arity-1)` is
            // first-applied -- see `call_ref`'s own docs and
            // `denote_closure`'s identical `AppShape::LitLambdaExact` arm).
            let mut call_args = Vec::with_capacity(1 + arity);
            if n_captures > 0 {
                let mk_env_expr = combinators.cp.mk_env_ref(&sig);
                call_args.push(apply_n(mk_env_expr, cs.iter().cloned()));
            }
            call_args.extend(ps.iter().rev().cloned());
            let lhs = apply_n(call_fn_here, call_args);

            // RHS: `h`'s own body, denoted with `params_full[i]` standing
            // for `Var(i)` (`denote`'s own convention) -- `0..arity` are
            // `h`'s own params (`ps`, in order); a capture's own `Var`
            // index is `arity + rel` for whatever relative index
            // `free_vars` found it at (`captures[j]`), *not* `arity + j`
            // -- `captures` isn't necessarily a dense `0..n_captures`
            // range, so `params_full` is sized to the largest relative
            // index actually used and filled sparsely, matching each
            // capture's own real `Var` position; any padding position
            // (never referenced by `body`, since `denote` only ever reads
            // a position some `Var(i)` in `body` actually names) holds an
            // arbitrary but well-typed filler.
            let mut params_full = ps.to_vec();
            if let Some(&max_rel) = captures.iter().max() {
                params_full.resize(arity + max_rel as usize + 1, cs[0].clone());
                for (j, &rel) in captures.iter().enumerate() {
                    params_full[arity + rel as usize] = cs[j].clone();
                }
            }
            let rhs = denote(store, body, &combinators.cp.arith, &params_full)?;

            let int_ty = combinators.cp.arith.int_ty();
            Some(kernel::id(int_ty, lhs, rhs))
        })?;
        let pos = self.cp.arith.p.push(ty);
        self.cp.call_eq_pos.insert(h, pos);
        Some(self.cp.arith.p.get(pos))
    }

    /// `clo_eq_ref`'s own sibling of `call_eq_ref`: a computation-rule
    /// axiom for `root`'s saturated call when it returns a `Clo_k`, not an
    /// `Int` (`combinator_return_type(root) == Some(Some(k))` --
    /// `call_eq_ref` itself owns the `Int` case and rejects this one).
    /// Needed for `AppShape::LitLambdaOver` (an over-applied literal
    /// lambda: `root`'s own saturated call produces a closure, then the
    /// *extra* arguments are dispatched against it directly) to get
    /// a concrete instance -- `mk_clo_ref`/`combinator_value`/
    /// `ite_clo_ref`/`pap_ref` are exactly as opaque as `call_ref` was
    /// before `call_eq_ref`, so the same "postulate a computation rule,
    /// sourced from `root`'s own real body, use via congruence" idiom
    /// applies one level up. See this module's own docs for why a
    /// per-call "trust the interpreter" shortcut would be circular
    /// instead.
    ///
    /// `root`'s own peeled body can never itself be a bare `Term::Abs`
    /// directly (`compile::peel`'s own `peel_abs` unconditionally folds
    /// every consecutive `Abs` layer into `root`'s own arity, confirmed
    /// empirically, not just by inspection, before settling on this
    /// restriction) -- a `Clo_k` result can only arise "one level down",
    /// via one of the shapes dispatched below: an `If` picking between two
    /// closures (`clo_eq_ref_if_tree`), a partial application of a
    /// further literal lambda (`clo_eq_ref_pap`), or a *saturated* call to
    /// a further literal lambda whose own saturated call is itself
    /// `Clo_k`-typed (`clo_eq_ref_call`, arbitrarily many such indirect
    /// calls deep). Checked at the Rust level (not merely inferred from
    /// `return_type_of`'s own structural classification, which would also
    /// accept a `Term::Rec` branch or a further nested `App`/`If` reached
    /// only through a captured/parameter variable, not a further
    /// statically-known literal lambda): those wider shapes have no way to
    /// produce a *concrete* closure descriptor below (a captured
    /// variable's own concrete identity is only knowable by executing, not
    /// by term shape -- see `RELATED_WORK.md` §9; `Term::Rec` inside a
    /// branch has no proof-side counterpart here), so they're rejected
    /// outright rather than mis-handled.
    pub(super) fn clo_eq_ref(&mut self, root: Hash) -> Option<(Expr, ClosureRhsShape)> {
        if let Some((pos, shape)) = self.cp.clo_eq_pos.get(&root) {
            let (pos, shape) = (*pos, shape.clone());
            return Some((self.cp.arith.p.get(pos), shape));
        }
        let (arity, body, is_rec) = compile::peel(self.store, root)?;
        // `root` *is* allowed to be self-recursive here now -- `compile::
        // free_vars`, `param_types_for`, and `combinator_return_type` are
        // all already `is_rec`-aware (the self-binder is excluded from
        // capture/param classification, and a genuine self-call inside
        // `body` structurally classifies as `Int`, per `return_type_of`'s
        // own `match_self_call` case, never `Term::Abs`/`Term::Rec`) -- so
        // a self-call appearing anywhere this construction would need a
        // concrete `Clo` value from (an `IfTree` leaf, or `Pap`/`Call`'s
        // own `g`) declines cleanly downstream by construction, without
        // this needing a special case: `combinator_return_type` returns
        // `None` if a self-call sits in a branch alongside a genuine
        // `Clo`-typed one (arity mismatch), and a bare self-call `Var`
        // never matches `Term::Abs`/`Term::Rec` when a leaf/`g` is
        // classified. `is_rec` is threaded into each branch below so its
        // own capture computation stays correct (excluding the self-binder
        // from the ordinary-capture list) instead of silently miscounting
        // it as one -- `clo_eq_ref_if_tree`/`clo_eq_ref_call`/
        // `clo_eq_ref_pap` previously hardcoded `false` here, which is why
        // this was declined outright before, not because any of the three
        // branches structurally can't handle a self-recursive `root`.
        let param_types = param_types_for(self.store, root)?;
        if param_types.iter().any(Option::is_some) {
            // Still declined: `root`'s own params_and_close_typed call
            // below quantifies every capture/param `Int`-typed
            // unconditionally (`quant_types`/`dummy_caller_param_types`
            // are both hardcoded all-`None` throughout `clo_eq_ref_if_tree`/
            // `clo_eq_ref_call`/`clo_eq_ref_pap`) -- a genuinely `Clo`-typed
            // parameter of `root` itself would need those widened to
            // root's own real `param_types`, a real but separate, larger
            // follow-on (touching the axiom's own quantification, not just
            // a capture-computation flag) not attempted here.
            return None;
        }
        let k = match combinator_return_type(self.store, root) {
            Some(Some(k)) => k,
            _ => return None,
        };
        match self.store.resolve(body) {
            Term::If(..) => self.clo_eq_ref_if_tree(root, arity, body, is_rec, k),
            // Tried in this order because they're mutually exclusive by
            // construction (each checks `args.len()` against `g`'s own
            // arity explicitly and declines otherwise), not because one is
            // more likely: `clo_eq_ref_call` only ever fires when `body`'s
            // own unwound spine is a *saturated* call to a further
            // `Clo_k`-returning combinator, `clo_eq_ref_pap` only when it's
            // a genuine partial application.
            Term::App(..) => self
                .clo_eq_ref_call(root, arity, body, is_rec, k)
                .or_else(|| self.clo_eq_ref_pap(root, arity, body, is_rec, &param_types, k)),
            _ => None,
        }
    }

    /// `clo_eq_ref`'s `If`-tree branch: `root`'s own body is an arbitrary
    /// tree of nested `If`s (`cond` at each node staying in the
    /// `Var`/`Lit`/`Prim`/`If` fragment), each leaf classified via
    /// `classify_closure_if_tree_leaf` into either a bare `Term::Abs`
    /// (never `Term::Rec`) or a partial application of a further literal
    /// lambda, both of arity `k` -- a flat `If(cond, t, e)` between two
    /// closures is just the depth-1, all-`Abs` case of this, no longer
    /// special-cased on its own.
    ///
    /// Every postulate this axiom's own RHS references (`register`'s own
    /// value expression for each `Abs` leaf, `pap_ref`'s for each `Pap`
    /// one, `mk_env_ref` for any leaf that captures, `ite_clo_ref(k)` for
    /// the `If` shape) may be pushed lazily from inside the
    /// `params_and_close_typed` closure below that binds `root`'s own
    /// quantified captures/params.
    pub(super) fn clo_eq_ref_if_tree(&mut self, root: Hash, arity: usize, body: Hash, is_rec: bool, k: usize) -> Option<(Expr, ClosureRhsShape)> {
        // Deliberately *not* `classify_tree` -- that function additionally
        // restricts every `cond` to a direct comparison
        // (`Lt`/`Le`/`Eq`), a `build_universal`-specific requirement
        // (`cond_premise`'s own use of plain `Id` equality) this
        // construction never needed even in its original flat form
        // (`cond` only ever needed to stay in the `Var`/`Lit`/`Prim`/`If`
        // fragment `denote`/`collect_literals` already cover) -- reusing
        // it here would silently narrow what already worked.
        let tree = classify_closure_if_tree(self.store, body);
        if matches!(tree, DecisionTree::Leaf(_)) {
            return None; // caller already matched Term::If on body directly
        }
        let leaf_shapes = classify_closure_if_tree_leaves(self.store, &tree, k)?;
        let shape = ClosureRhsShape::IfTree(tree.clone());

        let captures = compile::free_vars(self.store, body, arity, is_rec);
        let n_captures = captures.len();
        let dummy_caller_param_types: Vec<Option<usize>> =
            vec![None; captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let sig = capture_sig(&captures, &dummy_caller_param_types)?;

        // Literal pre-pass -- every `cond` in the tree, not `root`'s whole
        // body: `collect_literals` with `param_types: None`
        // unconditionally rejects any `Abs`/`App` it sees, and this
        // feature's entire premise is that `body` *contains* some (every
        // leaf) -- reusing `call_eq_ref`'s own whole-body pre-pass here
        // would reject every input outright. Every leaf's own body stays
        // opaque to this construction (its own literals are collected
        // later, when `call_eq_ref` runs on whichever one is concretely
        // chosen).
        let mut lits = Vec::new();
        if !collect_closure_if_tree_literals(self.store, &tree, arity, &mut lits) {
            return None;
        }
        for lit_n in lits {
            self.cp.arith.lit(lit_n);
        }

        let call_fn = self.call_ref(root, &captures, &dummy_caller_param_types)?;

        // Quantify `n_captures + arity` fresh `Int` postulates -- same
        // order (captures first, then `root`'s own params) `call_eq_ref`
        // itself uses.
        let quant_types = vec![None; n_captures + arity];
        let store = self.store;
        let ty = params_and_close_typed(self, &quant_types, kernel::Binder::Pi, |combinators, pp| {
            let (cs, ps) = pp.split_at(n_captures);
            let call_fn_here = call_fn.clone();

            // LHS: same construction as `call_eq_ref`'s own -- descending
            // `Var` order, matching `call_ref`'s own convention.
            let mut call_args = Vec::with_capacity(1 + arity);
            if n_captures > 0 {
                let mk_env_expr = combinators.cp.mk_env_ref(&sig);
                call_args.push(apply_n(mk_env_expr, cs.iter().cloned()));
            }
            call_args.extend(ps.iter().rev().cloned());
            let lhs = apply_n(call_fn_here, call_args);

            // `params_full`: same sparse capture-index construction
            // `call_eq_ref` uses for `root`'s own captures. Every leaf
            // sits at exactly `body`'s own scope depth (an `If`'s
            // branches introduce no binders, at any depth), so *their*
            // own relative capture indices (from `free_vars`, computed
            // against *their own* peeled arity) already land at the
            // correct *absolute* index into this same `params_full`
            // directly -- no additional `arity +` shift, unlike `root`'s
            // own captures just above (which genuinely need it, since
            // `root`'s own params occupy `0..arity` first).
            let mut params_full = ps.to_vec();
            if let Some(&max_rel) = captures.iter().max() {
                params_full.resize(arity + max_rel as usize + 1, cs[0].clone());
                for (j, &rel) in captures.iter().enumerate() {
                    params_full[arity + rel as usize] = cs[j].clone();
                }
            }

            // RHS: recursively `ite_clo_k(denote(cond, params_full),
            // <then's value>, <else's value>)` at every internal node,
            // bottoming out at each leaf's own `register`/`mk_env_ref`
            // value -- mirrors `denote_with_placeholders`'s own
            // `Term::If` (`Clo` branches) case structurally, generalized
            // from one step to the whole tree, over these abstract
            // quantified vars instead of a caller's real `params`.
            let rhs = build_closure_if_tree_rhs(store, combinators, &tree, &leaf_shapes, &params_full, k)?;

            let clo_ty = combinators.cp.clo_ty(k);
            Some(kernel::id(clo_ty, lhs, rhs))
        })?;
        let pos = self.cp.arith.p.push(ty);
        self.cp.clo_eq_pos.insert(root, (pos, shape.clone()));
        Some((self.cp.arith.p.get(pos), shape))
    }

    /// `clo_eq_ref`'s indirect-call branch: `root`'s own body is
    /// `g(args...)`, a *saturated* call to a further literal lambda `g`
    /// (`args.len()` exactly `g`'s own arity, `combinator_return_type(g) ==
    /// Some(k)` -- `g`'s own saturated call is itself `Clo_k`-typed, the
    /// same `k` as `root`'s own) -- the "further nested-call-producing
    /// root" shape: `root` doesn't itself hold the literal lambda that
    /// will eventually be called (unlike `Pap`'s own `g`, always the
    /// concrete answer), it only holds a further, statically-known
    /// *indirection* to one.
    ///
    /// The resulting axiom states `root`'s own call equals `call_ref(g)`
    /// applied to `args`'s own denoted values -- opaque, exactly like
    /// `Pap`'s own `pap_ref(g, s)(...)` RHS: it does *not* try to also
    /// unfold `g`'s own definition here (that would need `g`'s own shape,
    /// which may not even be known yet -- `clo_eq_ref(g)` is deliberately
    /// *not* called from here). Concrete resolution (finding the genuine
    /// literal-lambda leaf this indirection ultimately reaches, arbitrarily
    /// many `Call` hops deep) is a separate, later concern, handled
    /// recursively by `resolve_closure_shape_to_leaf` once an actual
    /// instance needs it -- mirroring how `Pap`'s own `g` isn't unfolded
    /// here either, just named.
    ///
    /// Well-founded for the same reason `combinator_return_type`'s own
    /// recursion into a further combinator's body is (see its own docs):
    /// hash-consing only ever lets `body` reference an *already-existing*
    /// `g`, so the "calls" relation between distinct combinators is a
    /// strict partial order matching construction order and can't cycle
    /// back to `root`.
    ///
    /// Restricted, like `clo_eq_ref_pap`, to `g`'s own params all being
    /// `Int`-typed; `args` themselves may be arbitrary `Var`/`Lit`/`Prim`/
    /// `If` expressions over `root`'s own scope (denoted via `denote`).
    ///
    /// `call_ref`/`mk_env_ref` for `root`'s own shape, `g`'s own
    /// `call_ref`/`mk_env_ref` too (needed directly in the RHS below,
    /// *not* `g`'s own `clo_eq_ref` axiom -- see above), may be pushed
    /// lazily from inside the `params_and_close_typed` closure that
    /// quantifies `root`'s own captures/params.
    pub(super) fn clo_eq_ref_call(&mut self, root: Hash, arity: usize, body: Hash, is_rec: bool, k: usize) -> Option<(Expr, ClosureRhsShape)> {
        let Shape::CombinatorCall { root: g, args, .. } = compile::classify(self.store, body, arity, is_rec.then_some(arity as u32)) else {
            return None;
        };
        let g_param_types = param_types_for(self.store, g)?;
        if g_param_types.iter().any(Option::is_some) {
            return None;
        }
        let g_arity = g_param_types.len();
        if args.len() != g_arity {
            return None; // under-applied -- clo_eq_ref_pap's own shape, not this one
        }
        if combinator_return_type(self.store, g) != Some(Some(k)) {
            return None;
        }
        let shape = ClosureRhsShape::Call { g, args: args.clone() };

        let captures = compile::free_vars(self.store, body, arity, is_rec);
        let n_captures = captures.len();
        let dummy_caller_param_types: Vec<Option<usize>> = vec![None; captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let sig = capture_sig(&captures, &dummy_caller_param_types)?;

        // Literal pre-pass -- every supplied arg, not `root`'s whole body
        // (mirrors `clo_eq_ref_pap`'s own `cond`-only-style pre-pass, for
        // the same reason).
        let mut lits = Vec::new();
        for &a in &args {
            if !collect_literals(self.store, a, arity, None, None, &mut lits) {
                return None;
            }
        }
        for lit_n in lits {
            self.cp.arith.lit(lit_n);
        }

        // `root`'s own shape, resolved (and, transitively, `mk_env_ref`
        // pushed as needed) before the quantified construction below.
        let call_fn = self.call_ref(root, &captures, &dummy_caller_param_types)?;
        let (g_arity2, g_body, g_is_rec) = compile::peel(self.store, g)?;
        let g_captures = compile::free_vars(self.store, g_body, g_arity2, g_is_rec);
        let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let g_call_fn = self.call_ref(g, &g_captures, &g_dummy)?;

        // Quantify `n_captures + arity` fresh `Int` postulates -- same
        // order `clo_eq_ref_pap`/`call_eq_ref` both use.
        let quant_types = vec![None; n_captures + arity];
        let store = self.store;
        let ty = params_and_close_typed(self, &quant_types, kernel::Binder::Pi, |combinators, pp| {
            let (cs, ps) = pp.split_at(n_captures);
            let call_fn_here = call_fn.clone();

            // LHS: identical construction to `clo_eq_ref_pap`'s own.
            let mut call_args = Vec::with_capacity(1 + arity);
            if n_captures > 0 {
                let mk_env_expr = combinators.cp.mk_env_ref(&sig);
                call_args.push(apply_n(mk_env_expr, cs.iter().cloned()));
            }
            call_args.extend(ps.iter().rev().cloned());
            let lhs = apply_n(call_fn_here, call_args);

            // `params_full`: identical sparse capture-index construction
            // to `clo_eq_ref_pap`'s own -- `body`'s own args sit at
            // exactly `body`'s own scope depth (a plain `App` introduces
            // no binders), so their relative indices land at the correct
            // absolute index directly.
            let mut params_full = ps.to_vec();
            if let Some(&max_rel) = captures.iter().max() {
                params_full.resize(arity + max_rel as usize + 1, cs[0].clone());
                for (j, &rel) in captures.iter().enumerate() {
                    params_full[arity + rel as usize] = cs[j].clone();
                }
            }

            // RHS: `call_ref(g)(g_env?, args...)` -- same argument
            // construction `clo_eq_ref_pap`'s own `pap_ref`-based RHS
            // uses, `call_ref(g)` in place of `pap_ref(g, s)`.
            let g_call_fn_here = g_call_fn.clone();
            let g_env = if g_captures.is_empty() {
                None
            } else {
                let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
                let mk_env_expr = combinators.cp.mk_env_ref(&g_sig);
                let cs2: Vec<Expr> = g_captures.iter().map(|&rel| params_full[rel as usize].clone()).collect();
                Some(apply_n(mk_env_expr, cs2))
            };
            let mut arg_exprs = Vec::with_capacity(args.len());
            for &a in &args {
                arg_exprs.push(denote(store, a, &combinators.cp.arith, &params_full)?);
            }
            let mut g_args = Vec::with_capacity(1 + args.len());
            g_args.extend(g_env);
            g_args.extend(arg_exprs);
            let rhs = apply_n(g_call_fn_here, g_args);

            let clo_ty = combinators.cp.clo_ty(k);
            Some(kernel::id(clo_ty, lhs, rhs))
        })?;
        let pos = self.cp.arith.p.push(ty);
        self.cp.clo_eq_pos.insert(root, (pos, shape.clone()));
        Some((self.cp.arith.p.get(pos), shape))
    }

    /// `clo_eq_ref`'s partial-application branch: `root`'s own body is
    /// `g(args...)`, a partial application of a further literal lambda `g`
    /// (own arity strictly greater than `args.len()`, `k = g`'s own arity
    /// minus `args.len()`) -- no branching at all, so the *only* possible
    /// resulting `Clo_k` value is `pap_ref(g, args.len())` applied to
    /// `args`'s own denoted values. Restricted to `g`'s own params all
    /// being `Int`-typed (mirroring `call_eq_ref`'s identical restriction
    /// on `root`'s own): `args` themselves may be arbitrary
    /// `Var`/`Lit`/`Prim`/`If` expressions over `root`'s own scope
    /// (denoted via `denote`), just never another closure-producing call
    /// of their own -- widening that is a separate, not-yet-attempted
    /// follow-on (see `RELATED_WORK.md`).
    ///
    /// `call_ref`/`mk_env_ref` for `root`'s own shape, `pap_ref`/
    /// `mk_env_ref` for `g`'s, may be pushed lazily from inside the
    /// `params_and_close_typed` closure that quantifies `root`'s own
    /// captures/params.
    pub(super) fn clo_eq_ref_pap(&mut self, root: Hash, arity: usize, body: Hash, is_rec: bool, _param_types: &[Option<usize>], k: usize) -> Option<(Expr, ClosureRhsShape)> {
        let Shape::CombinatorCall { root: g, args, .. } = compile::classify(self.store, body, arity, is_rec.then_some(arity as u32)) else {
            return None;
        };
        let g_param_types = param_types_for(self.store, g)?;
        if g_param_types.iter().any(Option::is_some) {
            return None;
        }
        let g_arity = g_param_types.len();
        if args.len() >= g_arity || g_arity - args.len() + pap_extra_arity(self.store, g) != k {
            return None;
        }
        let shape = ClosureRhsShape::Pap { g, args: args.clone() };

        let captures = compile::free_vars(self.store, body, arity, is_rec);
        let n_captures = captures.len();
        let dummy_caller_param_types: Vec<Option<usize>> =
            vec![None; captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let sig = capture_sig(&captures, &dummy_caller_param_types)?;

        // Literal pre-pass -- every supplied arg, not `root`'s whole body
        // (mirrors `clo_eq_ref_if_tree`'s own `cond`-only pre-pass, for
        // the same reason: `collect_literals` unconditionally rejects the
        // `App` this whole shape's premise requires). `g`'s own body stays
        // opaque to this construction, exactly like `t`/`e`'s own bodies
        // in the `If` case -- its own literals are collected later, when
        // `call_eq_ref` runs on `g` concretely (`eval_and_prove_direct_call`).
        let mut lits = Vec::new();
        for &a in &args {
            if !collect_literals(self.store, a, arity, None, None, &mut lits) {
                return None;
            }
        }
        for lit_n in lits {
            self.cp.arith.lit(lit_n);
        }

        // `root`'s own shape, resolved (and, transitively, `mk_env_ref`
        // pushed as needed) before the quantified construction below.
        let call_fn = self.call_ref(root, &captures, &dummy_caller_param_types)?;
        let (_, g_body, g_is_rec) = compile::peel(self.store, g)?;
        let g_captures = compile::free_vars(self.store, g_body, g_arity, g_is_rec);
        let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let pap_fn = self.pap_ref(g, args.len(), &g_dummy)?;

        // Quantify `n_captures + arity` fresh `Int` postulates -- same
        // order `clo_eq_ref_if_tree`/`call_eq_ref` both use.
        let quant_types = vec![None; n_captures + arity];
        let store = self.store;
        let ty = params_and_close_typed(self, &quant_types, kernel::Binder::Pi, |combinators, pp| {
            let (cs, ps) = pp.split_at(n_captures);
            let call_fn_here = call_fn.clone();

            // LHS: identical construction to `clo_eq_ref_if_tree`'s own.
            let mut call_args = Vec::with_capacity(1 + arity);
            if n_captures > 0 {
                let mk_env_expr = combinators.cp.mk_env_ref(&sig);
                call_args.push(apply_n(mk_env_expr, cs.iter().cloned()));
            }
            call_args.extend(ps.iter().rev().cloned());
            let lhs = apply_n(call_fn_here, call_args);

            // `params_full`: identical sparse capture-index construction
            // to `clo_eq_ref_if_tree`'s own -- `body`'s own args sit at
            // exactly `body`'s own scope depth (a plain `App` introduces
            // no binders), so their relative indices land at the correct
            // absolute index directly.
            let mut params_full = ps.to_vec();
            if let Some(&max_rel) = captures.iter().max() {
                params_full.resize(arity + max_rel as usize + 1, cs[0].clone());
                for (j, &rel) in captures.iter().enumerate() {
                    params_full[arity + rel as usize] = cs[j].clone();
                }
            }

            // RHS: `pap_ref(g, s)(g_env?, args...)` -- same argument
            // construction (application order, `g`'s own `param_types` at
            // each position) `denote_closure`'s own `LitLambdaPartial` arm
            // uses, over `params_full` (abstract quantified vars) instead
            // of a caller's real frame.
            let pap_fn_here = pap_fn.clone();
            let g_env = if g_captures.is_empty() {
                None
            } else {
                let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
                let mk_env_expr = combinators.cp.mk_env_ref(&g_sig);
                let cs2: Vec<Expr> = g_captures.iter().map(|&rel| params_full[rel as usize].clone()).collect();
                Some(apply_n(mk_env_expr, cs2))
            };
            let mut arg_exprs = Vec::with_capacity(args.len());
            for &a in &args {
                arg_exprs.push(denote(store, a, &combinators.cp.arith, &params_full)?);
            }
            let mut pap_args = Vec::with_capacity(1 + args.len());
            pap_args.extend(g_env);
            pap_args.extend(arg_exprs);
            let rhs = apply_n(pap_fn_here, pap_args);

            let clo_ty = combinators.cp.clo_ty(k);
            Some(kernel::id(clo_ty, lhs, rhs))
        })?;
        let pos = self.cp.arith.p.push(ty);
        self.cp.clo_eq_pos.insert(root, (pos, shape.clone()));
        Some((self.cp.arith.p.get(pos), shape))
    }

    /// `assume_ite_fact`'s counterpart for `ite_clo_arity`, generalized:
    /// `ite_clo_arity` has no computation rule either, but unlike
    /// `assume_ite_fact` (which memoizes per exact literal `(c,t,e)`
    /// triple, since `Int` branches *are* literals), the two branches
    /// here are `Clo`-typed *expressions* -- not simple values -- so `dt`/
    /// `de` are quantified generically over instead: `Pi dt: Clo_arity.
    /// Pi de: Clo_arity. Id(Clo_arity, ite_clo_arity(lit_ref(xc), dt, de),
    /// if xc != 0 {dt} else {de})`. Memoized by `(xc, arity)` -- keyed by
    /// the actual concrete condition value, exactly like
    /// `assume_ite_fact`'s own `(c,t,e)` key, *not* a collapsed boolean:
    /// `clo_eq_ref`'s own RHS embeds `ite_clo_k(denote(cond, ...), ..)`,
    /// and once instantiated at literals that first argument is whatever
    /// `denote(cond, lits)` produces -- a compound, unreduced postulated-
    /// arithmetic term (e.g. `app2(op_ref(Lt), lit_ref(0), lit_ref(a))`
    /// for `cond = 0 < a`), never syntactically `lit_ref(1)`/`lit_ref(0)`
    /// no matter what it numerically evaluates to (postulates have no
    /// computation rule; a general `If` condition isn't even guaranteed
    /// boolean-valued). Callers bridge that first argument to `lit_ref(xc)`
    /// via an explicit `cong1` step of their own (using whatever proof
    /// `eval_and_prove`'s own recursive call on `cond` already produced)
    /// *before* `trans_proof`-chaining this axiom's own instantiation in --
    /// the same "`cong_n` can't span a heterogeneous domain" workaround
    /// `eval_and_prove_direct_call` already needs for `call_ref`'s own
    /// `Env_sig`+`Int` mix (`ite_clo_ref`'s own type is `Int -> Clo_arity
    /// -> Clo_arity -> Clo_arity`, heterogeneous, so one `cong_n` spanning
    /// all three arguments -- the way `eval_and_prove`'s own `Term::If`
    /// case does for the all-`Int` `ite_ref` -- isn't available here).
    pub(super) fn ite_clo_eq_ref(&mut self, xc: i64, arity: usize) -> Expr {
        let key = (xc, arity);
        if let Some(&pos) = self.cp.ite_clo_eq_pos.get(&key) {
            return self.cp.arith.p.get(pos);
        }
        self.cp.arith.lit(xc);
        let clo_ty = self.cp.clo_ty(arity);
        let ite_clo = self.cp.ite_clo_ref(arity);
        let lit_xc = self.cp.arith.lit_ref(xc);
        // `dt`/`de` : `Clo_arity` -- `params_and_close` itself can only
        // ever push `Int`-typed postulates (it doesn't even take a
        // `ClosureCombinators`), so this needs `params_and_close_typed`'s
        // own `Clo_k`-aware quantification instead.
        let quant_types = vec![Some(arity), Some(arity)];
        let ty = params_and_close_typed(self, &quant_types, kernel::Binder::Pi, |_combinators, pp| {
            let (dt, de) = (pp[0].clone(), pp[1].clone());
            let clo_ty_here = clo_ty.clone();
            let ite_clo_here = ite_clo.clone();
            let lit_xc_here = lit_xc.clone();
            let lhs = kernel::app3(ite_clo_here, lit_xc_here, dt.clone(), de.clone());
            let rhs = if xc != 0 { dt } else { de };
            Some(kernel::id(clo_ty_here, lhs, rhs))
        })
        .expect("the build closure above always returns Some");
        let pos = self.cp.arith.p.push(ty);
        self.cp.ite_clo_eq_pos.insert(key, pos);
        self.cp.arith.p.get(pos)
    }

    /// Ties `inner_root`'s own closure *value* (whatever
    /// `register(inner_root)` produces, called directly with `arity`
    /// `Int` arguments -- a `Clo_k`-typed value *is* the real curried
    /// `Int -> .. -> Int` arrow type now, see `RELATED_WORK.md` section
    /// 11, so no separate "how to call this" axiom is needed the way
    /// `apply_ref` used to be) to `call_ref(inner_root)`:
    /// `<inner_root's own value>(env?)(p_{k-1}..p_0) =
    /// call_ref(inner_root)(env?, p_{k-1}..p_0)`, quantified over
    /// `inner_root`'s own captures then its own `k` params (same shape,
    /// same descending param order, as `call_eq_ref`'s own
    /// quantification), memoized by `inner_root` alone. Still genuinely
    /// postulated, not derivable: `register(inner_root)`/`call_ref
    /// (inner_root)` remain two independently postulated opaque
    /// constants (see `RELATED_WORK.md` section 11's own second
    /// correction for why `Clo_k` becoming transparent doesn't relate
    /// them to each other on its own) -- but honest for the same reason
    /// `call_eq_ref` is: `register`'s and `mk_clo_ref`'s combined meaning
    /// *is* "calling the closure that value represents", so relating it to
    /// `call_ref(inner_root)` (already pinned by `call_eq_ref`) states
    /// nothing new, just makes the connection kernel-checkable. Every
    /// postulate this references may be pushed lazily from inside the
    /// quantified construction below.
    pub(super) fn apply_clo_eq_ref(&mut self, inner_root: Hash) -> Option<Expr> {
        if let Some(&pos) = self.cp.apply_clo_eq_pos.get(&inner_root) {
            return Some(self.cp.arith.p.get(pos));
        }
        let (arity, body, is_rec) = compile::peel(self.store, inner_root)?;
        if is_rec {
            return None;
        }
        let param_types = param_types_for(self.store, inner_root)?;
        if param_types.iter().any(Option::is_some) {
            return None;
        }
        let captures = compile::free_vars(self.store, body, arity, is_rec);
        let n_captures = captures.len();
        let dummy_caller_param_types: Vec<Option<usize>> =
            vec![None; captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let sig = capture_sig(&captures, &dummy_caller_param_types)?;

        let call_fn = self.call_ref(inner_root, &captures, &dummy_caller_param_types)?;
        let value_fn = self.register(inner_root, &captures, &dummy_caller_param_types)?;

        let quant_types = vec![None; n_captures + arity];
        let ty = params_and_close_typed(self, &quant_types, kernel::Binder::Pi, |combinators, pp| {
            let (cs, ps) = pp.split_at(n_captures);
            let value_fn_here = value_fn.clone();
            let call_fn_here = call_fn.clone();

            let (closure_value, env_arg): (Expr, Option<Expr>) = if n_captures > 0 {
                let mk_env_expr = combinators.cp.mk_env_ref(&sig);
                let env = apply_n(mk_env_expr, cs.iter().cloned());
                (kernel::app(value_fn_here, env.clone()), Some(env))
            } else {
                (value_fn_here, None)
            };

            // LHS: `closure_value` is itself the real curried arrow type
            // now, so calling it with `arity` arguments is ordinary
            // application -- no `apply_ref` axiom to route through.
            let lhs = apply_n(closure_value, ps.iter().rev().cloned());

            // RHS: `call_ref(inner_root)(env?, p_{k-1}..p_0)` -- same
            // combinator, same descending params, `env` (if any) leading,
            // matching `call_ref`'s own convention exactly.
            let mut call_args = Vec::with_capacity(1 + arity);
            call_args.extend(env_arg);
            call_args.extend(ps.iter().rev().cloned());
            let rhs = apply_n(call_fn_here, call_args);

            let int_ty = combinators.cp.arith.int_ty();
            Some(kernel::id(int_ty, lhs, rhs))
        })?;
        let pos = self.cp.arith.p.push(ty);
        self.cp.apply_clo_eq_pos.insert(inner_root, pos);
        Some(self.cp.arith.p.get(pos))
    }

    /// `apply_clo_eq_ref`'s own counterpart for a `Clo_k` value that's a
    /// *partial application* (`pap_ref(g, s)`'s own value) rather than a
    /// directly-registered combinator's: `pap_ref(g,
    /// s)(g_env?, a_{s-1}..a_0)(b_{k-1}..b_0) = call_ref(g)(g_env?,
    /// a_{s-1}..a_0, b_{k-1}..b_0)`, `k = g`'s own arity minus `s`, the
    /// left side called directly (a `Clo_k` value is the real curried
    /// `Int -> .. -> Int` arrow type, see `RELATED_WORK.md` section 11 --
    /// no separate "how to call this" axiom needed). Needed because
    /// `pap_ref` is exactly as opaque as a directly-registered
    /// combinator's own value was before `apply_clo_eq_ref` -- this is the
    /// semantic fact a compile-time-desugared PAP wrapper's own codegen
    /// encodes (`register_partial_app`'s wrapper forwards its own
    /// supplied arguments plus whatever further ones it's eventually
    /// given straight into `g`'s own entry), stated here as the only thing
    /// that gives `pap_ref`'s otherwise-opaque value defined behavior once
    /// something is actually applied to it. Restricted to `g`'s own
    /// params all being `Int`-typed, mirroring `clo_eq_ref_pap`'s own
    /// identical restriction (this axiom is only ever reached from there).
    /// Memoized by `(g, s)` alone -- `pap_ref(g, s)` stays memoized by its
    /// own key already.
    pub(super) fn apply_pap_eq_ref(&mut self, g: Hash, s: usize) -> Option<Expr> {
        let key = (g, s);
        if let Some(&pos) = self.cp.apply_pap_eq_pos.get(&key) {
            return Some(self.cp.arith.p.get(pos));
        }
        let (g_arity, g_body, g_is_rec) = compile::peel(self.store, g)?;
        if s == 0 || s >= g_arity {
            return None;
        }
        let g_param_types = param_types_for(self.store, g)?;
        if g_param_types.iter().any(Option::is_some) {
            return None;
        }
        let g_captures = compile::free_vars(self.store, g_body, g_arity, g_is_rec);
        let n_captures = g_captures.len();
        let dummy_caller_param_types: Vec<Option<usize>> =
            vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let sig = capture_sig(&g_captures, &dummy_caller_param_types)?;

        let call_fn = self.call_ref(g, &g_captures, &dummy_caller_param_types)?;
        let pap_fn = self.pap_ref(g, s, &dummy_caller_param_types)?;

        // Quantify `n_captures + g_arity` fresh `Int` postulates -- same
        // order (captures first, then `g`'s own `s` supplied params, then
        // its remaining `k`) `apply_clo_eq_ref`'s own quantification uses
        // for captures-then-params.
        let quant_types = vec![None; n_captures + g_arity];
        let ty = params_and_close_typed(self, &quant_types, kernel::Binder::Pi, |combinators, pp| {
            let (cs, ps) = pp.split_at(n_captures);
            let (supplied, more) = ps.split_at(s);
            let pap_fn_here = pap_fn.clone();
            let call_fn_here = call_fn.clone();

            let (pap_value, env_arg): (Expr, Option<Expr>) = if n_captures > 0 {
                let mk_env_expr = combinators.cp.mk_env_ref(&sig);
                let env = apply_n(mk_env_expr, cs.iter().cloned());
                let v = apply_n(pap_fn_here, std::iter::once(env.clone()).chain(supplied.iter().cloned()));
                (v, Some(env))
            } else {
                (apply_n(pap_fn_here, supplied.iter().cloned()), None)
            };

            // LHS: `pap_value(more_{k-1}..more_0)`, called directly -- the
            // same descending order this axiom's own construction (and
            // `apply_clo_eq_ref`'s) has always applied its own trailing
            // `Int` params in: `pap_ref(g,s)`'s own codomain *is*
            // `curried_int_ty(k)`.
            let lhs = apply_n(pap_value, more.iter().rev().cloned());

            // RHS: `call_ref(g)(g_env?, a_0..a_{s-1}, b_{k-1}..b_0)` --
            // same combinator, `g`'s own full argument list in one call,
            // `env` (if any) leading. The `s` supplied args are *not*
            // reversed here, unlike `more`: they only ever pass through
            // `pap_fn`'s own convention (unreversed, on the LHS) -- so
            // their own ordering only has to agree between this axiom's
            // LHS and RHS (and whatever independently reconstructs the
            // same value at a call site, e.g. `eval_and_prove_call_over`'s
            // own `pap_at_denoted`), not with `call_ref`'s "descending"
            // convention the way `more` must.
            let mut call_args = Vec::with_capacity(1 + s + more.len());
            call_args.extend(env_arg);
            call_args.extend(supplied.iter().cloned());
            call_args.extend(more.iter().rev().cloned());
            let rhs = apply_n(call_fn_here, call_args);

            let int_ty = combinators.cp.arith.int_ty();
            Some(kernel::id(int_ty, lhs, rhs))
        })?;
        let pos = self.cp.arith.p.push(ty);
        self.cp.apply_pap_eq_pos.insert(key, pos);
        Some(self.cp.arith.p.get(pos))
    }
}

/// `root`'s own body, as `clo_eq_ref` requires it -- carried alongside its
/// memoized axiom so a memo hit doesn't need to re-classify `root`'s
/// body, and so `eval_and_prove_call_over` knows which `Hash`es to
/// concretely evaluate. `root`'s own peeled body can never itself be a
/// bare literal lambda directly (`compile::peel`'s own `peel_abs` always
/// folds every consecutive `Abs` layer into `root`'s own arity, so a
/// `Clo_k`-returning saturated call can only arise "one level down"), so
/// every variant here describes some further, `Abs`-nested computation.
#[derive(Clone)]
pub(super) enum ClosureRhsShape {
    /// An arbitrary tree of nested `If`s, each leaf a same-arity literal
    /// lambda -- a flat `If(cond, inner_t, inner_e)` between two closures
    /// is just the depth-1 case.
    IfTree(DecisionTree),
    /// `g(args...)`, a partial application of a literal lambda `g` (own
    /// arity strictly greater than `args.len()`) -- no branching at all,
    /// the *only* possible resulting `Clo_k` value is `pap_ref(g,
    /// args.len())` applied to `args`'s own denoted values.
    Pap { g: Hash, args: Vec<Hash> },
    /// `g(args...)`, a *saturated* call to a further literal lambda `g`
    /// (`args.len()` exactly `g`'s own arity) whose own saturated call is
    /// itself `Clo_k`-typed (`combinator_return_type(g) == Some(k)`,
    /// which already classifies this recursively -- see its own docs) --
    /// a genuinely *indirect* call, one level further than `Pap`'s own
    /// direct partial application. The resulting `Clo_k` value is
    /// `call_ref(g)` applied to `args`'s own denoted values; *which*
    /// concrete literal lambda that ultimately is stays opaque to this
    /// axiom itself, exactly like `Pap`'s own `g` does -- resolved later,
    /// recursively, by whichever consumer needs a concrete instance (see
    /// `resolve_closure_shape_to_leaf`).
    Call { g: Hash, args: Vec<Hash> },
}

/// Classifies `h` into a [`DecisionTree`] for `clo_eq_ref_if_tree`'s own
/// purposes -- structurally identical to `classify_tree`, but *without*
/// that function's own restriction of every `cond` to a direct
/// comparison (`build_universal`'s own `cond_premise` needs that for its
/// plain-`Id`-equality gating; this construction never did, even in its
/// original flat form -- `cond` only ever needed to stay in the
/// `Var`/`Lit`/`Prim`/`If` fragment `denote`/`collect_literals` already
/// cover). Always succeeds -- whether every leaf is actually a bare
/// `Term::Abs` of the right arity is `closure_if_tree_leaves_are_abs`'s
/// own, separate question.
pub(super) fn classify_closure_if_tree(store: &TermStore, h: Hash) -> DecisionTree {
    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        return DecisionTree::If {
            cond: c,
            then_branch: Box::new(classify_closure_if_tree(store, t)),
            else_branch: Box::new(classify_closure_if_tree(store, e)),
        };
    }
    DecisionTree::Leaf(h)
}

/// A single `IfTree` leaf's own resolved shape -- generalizes the
/// original "every leaf is a bare `Term::Abs`" restriction to also allow
/// a leaf that's itself a partial application of a further literal
/// lambda (mirroring `ClosureRhsShape::Pap`, but keyed per leaf instead
/// of per `root`; README's own "still open" note on "a partially-applied
/// closure creation in this position"), or a leaf reached only through a
/// further *saturated* indirect call to a further literal lambda `g`
/// whose own saturated call is itself `Clo_k`-typed (mirroring
/// `ClosureRhsShape::Call`, keyed per leaf instead of per `root`).
pub(super) enum ClosureIfTreeLeafShape {
    Abs { captures: Vec<u32> },
    Pap { g: Hash, args: Vec<Hash> },
    Call { g: Hash, args: Vec<Hash> },
}

/// Classifies one `IfTree` leaf `h`: a bare literal lambda (`Abs`,
/// captures via `free_vars`, `Term::Rec` excluded -- no proof-side
/// counterpart here, same restriction the original all-`Abs` check
/// already made), a partial application `g(args)` of a further literal
/// lambda `g`, under-applied by exactly `k` (`root`'s own expected `Clo`
/// arity, already confirmed shared by every leaf via
/// `combinator_return_type`'s own recursion before `clo_eq_ref_if_tree`
/// is ever reached -- mirrors `clo_eq_ref_pap`'s own classification,
/// restricted the same way to `g`'s own params all being `Int`-typed), or
/// a *saturated* call `g(args)` whose own saturated call is itself
/// `Clo_k`-typed (mirrors `clo_eq_ref_call`'s own classification and
/// restriction). `None` for anything else (a further nested `If`/`Rec`,
/// an unrecognized `App` shape).
pub(super) fn classify_closure_if_tree_leaf(store: &TermStore, h: Hash, k: usize) -> Option<ClosureIfTreeLeafShape> {
    match compile::classify(store, h, 0, None) {
        Shape::Combinator { is_rec: false } => {
            let (inner_arity, inner_body, inner_is_rec) = compile::peel(store, h)?;
            let captures = compile::free_vars(store, inner_body, inner_arity, inner_is_rec);
            Some(ClosureIfTreeLeafShape::Abs { captures })
        }
        Shape::CombinatorCall { root: g, args, .. } => {
            let g_param_types = param_types_for(store, g)?;
            if g_param_types.iter().any(Option::is_some) {
                return None;
            }
            let g_arity = g_param_types.len();
            if args.len() == g_arity {
                if combinator_return_type(store, g) != Some(Some(k)) {
                    return None;
                }
                Some(ClosureIfTreeLeafShape::Call { g, args })
            } else if args.len() < g_arity && g_arity - args.len() + pap_extra_arity(store, g) == k {
                Some(ClosureIfTreeLeafShape::Pap { g, args })
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Every leaf of `tree`, classified via `classify_closure_if_tree_leaf`
/// (a leaf appearing more than once in the tree -- structurally
/// identical sub-terms, hash-consed together -- classified only once);
/// `None` if any leaf fails to classify.
pub(super) fn classify_closure_if_tree_leaves(store: &TermStore, tree: &DecisionTree, k: usize) -> Option<HashMap<Hash, ClosureIfTreeLeafShape>> {
    let mut leaves = Vec::new();
    closure_if_tree_leaves(tree, &mut leaves);
    let mut shapes = HashMap::new();
    for h in leaves {
        if shapes.contains_key(&h) {
            continue;
        }
        shapes.insert(h, classify_closure_if_tree_leaf(store, h, k)?);
    }
    Some(shapes)
}

/// Every leaf `Hash` of `tree`, left-to-right/depth-first (matching
/// `flatten_tree`'s own leaf-visiting order, though nothing here
/// currently depends on the exact order -- kept for consistency).
pub(super) fn closure_if_tree_leaves(tree: &DecisionTree, out: &mut Vec<Hash>) {
    match tree {
        DecisionTree::Leaf(h) => out.push(*h),
        DecisionTree::If { then_branch, else_branch, .. } => {
            closure_if_tree_leaves(then_branch, out);
            closure_if_tree_leaves(else_branch, out);
        }
    }
}

/// `collect_literals` over every `cond` in `tree`, generalizing
/// `clo_eq_ref_if_tree`'s own single-condition pre-pass to however many
/// internal nodes the tree actually has. `Pap`-shaped leaves' own
/// supplied `args` are *not* collected here, mirroring `clo_eq_ref_pap`'s
/// own identical choice -- their own literals are collected later, when
/// `eval_and_prove`/`denote` actually runs on them.
pub(super) fn collect_closure_if_tree_literals(store: &TermStore, tree: &DecisionTree, arity: usize, lits: &mut Vec<i64>) -> bool {
    match tree {
        DecisionTree::Leaf(_) => true,
        DecisionTree::If { cond, then_branch, else_branch } => {
            collect_literals(store, *cond, arity, None, None, lits)
                && collect_closure_if_tree_literals(store, then_branch, arity, lits)
                && collect_closure_if_tree_literals(store, else_branch, arity, lits)
        }
    }
}

/// An `Abs`-shaped leaf's own `register`/`mk_env_ref` value expression,
/// over abstract `params_full` -- `clo_eq_ref_if_tree`'s own single-pair
/// `value_expr`, generalized to read a leaf's own captures from
/// `captures` (from `leaf_shapes`) instead of a locally-closed-over pair.
pub(super) fn closure_leaf_value_expr(combinators: &mut ClosureCombinators<'_>, leaf: Hash, captures: &[u32], params_full: &[Expr]) -> Option<Expr> {
    let dummy: Vec<Option<usize>> = vec![None; captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let sym = combinators.register(leaf, captures, &dummy)?;
    if captures.is_empty() {
        Some(sym)
    } else {
        let sig: Vec<Option<usize>> = vec![None; captures.len()];
        let mk_env_expr = combinators.cp.mk_env_ref(&sig);
        let cs2: Vec<Expr> = captures.iter().map(|&rel| params_full[rel as usize].clone()).collect();
        Some(kernel::app(sym, apply_n(mk_env_expr, cs2)))
    }
}

/// A `Pap`-shaped leaf's own `pap_ref`/`mk_env_ref` value expression,
/// over abstract `params_full` -- mirrors `clo_eq_ref_pap`'s own
/// RHS-formula construction exactly (same `pap_ref(g,s)(g_env?,
/// denote(args, params_full)...)`), just built over `root`'s own
/// abstract quantified vars here instead of a fresh `Pi`'s own.
pub(super) fn closure_leaf_pap_value_expr(store: &TermStore, combinators: &mut ClosureCombinators<'_>, g: Hash, args: &[Hash], params_full: &[Expr]) -> Option<Expr> {
    let (g_arity, g_body, g_is_rec) = compile::peel(store, g)?;
    let g_captures = compile::free_vars(store, g_body, g_arity, g_is_rec);
    let s = args.len();
    let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let pap_fn = combinators.pap_ref(g, s, &g_dummy)?;
    let g_env = if g_captures.is_empty() {
        None
    } else {
        let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
        let mk_env_expr = combinators.cp.mk_env_ref(&g_sig);
        let cs2: Vec<Expr> = g_captures.iter().map(|&rel| params_full[rel as usize].clone()).collect();
        Some(apply_n(mk_env_expr, cs2))
    };
    let mut arg_exprs = Vec::with_capacity(s);
    for &a in args {
        arg_exprs.push(denote(store, a, &combinators.cp.arith, params_full)?);
    }
    let mut pap_args = Vec::with_capacity(1 + s);
    pap_args.extend(g_env);
    pap_args.extend(arg_exprs);
    Some(apply_n(pap_fn, pap_args))
}

/// A `Call`-shaped leaf's own `call_ref`/`mk_env_ref` value expression,
/// over abstract `params_full` -- mirrors `clo_eq_ref_call`'s own
/// RHS-formula construction exactly (`call_ref(g)(g_env?, denote(args,
/// params_full)...)`), just built over `root`'s own abstract quantified
/// vars here instead of a fresh `Pi`'s own.
pub(super) fn closure_leaf_call_value_expr(store: &TermStore, combinators: &mut ClosureCombinators<'_>, g: Hash, args: &[Hash], params_full: &[Expr]) -> Option<Expr> {
    let (g_arity, g_body, g_is_rec) = compile::peel(store, g)?;
    let g_captures = compile::free_vars(store, g_body, g_arity, g_is_rec);
    let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let call_fn = combinators.call_ref(g, &g_captures, &g_dummy)?;
    let g_env = if g_captures.is_empty() {
        None
    } else {
        let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
        let mk_env_expr = combinators.cp.mk_env_ref(&g_sig);
        let cs2: Vec<Expr> = g_captures.iter().map(|&rel| params_full[rel as usize].clone()).collect();
        Some(apply_n(mk_env_expr, cs2))
    };
    let mut arg_exprs = Vec::with_capacity(args.len());
    for &a in args {
        arg_exprs.push(denote(store, a, &combinators.cp.arith, params_full)?);
    }
    let mut call_args = Vec::with_capacity(1 + arg_exprs.len());
    call_args.extend(g_env);
    call_args.extend(arg_exprs);
    Some(apply_n(call_fn, call_args))
}

/// `clo_eq_ref_if_tree`'s own axiom RHS, built recursively over `tree`:
/// `ite_clo_k(denote(cond, params_full), <then's value>, <else's value>)`
/// at every internal node, bottoming out at each leaf's own value
/// expression (`closure_leaf_value_expr` for `Abs`,
/// `closure_leaf_pap_value_expr` for `Pap`, `closure_leaf_call_value_expr`
/// for `Call`, dispatched via `leaf_shapes`). Mirrors
/// `denote_with_placeholders`'s own `Term::If` (`Clo` branches) case
/// structurally, generalized from one step to the whole tree.
pub(super) fn build_closure_if_tree_rhs(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    tree: &DecisionTree,
    leaf_shapes: &HashMap<Hash, ClosureIfTreeLeafShape>,
    params_full: &[Expr],
    k: usize,
) -> Option<Expr> {
    match tree {
        DecisionTree::Leaf(h) => match leaf_shapes.get(h)? {
            ClosureIfTreeLeafShape::Abs { captures } => closure_leaf_value_expr(combinators, *h, captures, params_full),
            ClosureIfTreeLeafShape::Pap { g, args } => closure_leaf_pap_value_expr(store, combinators, *g, args, params_full),
            ClosureIfTreeLeafShape::Call { g, args } => closure_leaf_call_value_expr(store, combinators, *g, args, params_full),
        },
        DecisionTree::If { cond, then_branch, else_branch } => {
            let dc = denote(store, *cond, &combinators.cp.arith, params_full)?;
            let dt = build_closure_if_tree_rhs(store, combinators, then_branch, leaf_shapes, params_full, k)?;
            let de = build_closure_if_tree_rhs(store, combinators, else_branch, leaf_shapes, params_full, k)?;
            let ite_clo = combinators.cp.ite_clo_ref(k);
            Some(kernel::app3(ite_clo, dc, dt, de))
        }
    }
}

/// A `Pap`-shaped leaf's own concrete literal value, `g`'s own captures
/// and supplied args each resolved to literal triples -- the `Pap`-shaped
/// sibling of `inner_closure_literal_value`, mirroring
/// `eval_and_prove_call_over`'s own `Pap` arm's `pap_at_denoted`
/// construction exactly (same `pap_ref(g,s)(g_env?, ...)` formula, over
/// `root`'s own literal inner frame instead of the outer caller's).
/// Returns `(pap_value, g_cap_triples, supplied_triples)` -- the latter
/// two needed by `resolve_closure_if_tree` so `g`, once finally chosen,
/// gets called with its own supplied args *and* whatever extra args the
/// outer over-application supplies, not just the extra ones (`Pap`'s own
/// convention -- see `resolve_closure_shape_to_leaf`).
pub(super) fn inner_closure_pap_value(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    g: Hash,
    args: &[Hash],
    inner_params: &[Expr],
    inner_concrete: &[i64],
    inner_facts: &[Expr],
) -> Option<(Expr, ValueTriples, ValueTriples)> {
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

    let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let pap_fn = combinators.pap_ref(g, s, &g_dummy)?;
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
    let pap_value = apply_n(pap_fn, pap_args);
    Some((pap_value, g_cap_triples, supplied_triples))
}

/// A `Call`-shaped leaf's own concrete literal value -- the `Call`-shaped
/// sibling of `inner_closure_pap_value`, mirroring
/// `closure_leaf_call_value_expr`'s own formula (`call_ref(g)(g_env?,
/// denote(args, ...))`) over `root`'s own literal inner frame instead of
/// abstract quantified vars. Deliberately *not* built via
/// `build_clo_call_bridge` (which would eagerly force `g`'s own
/// `clo_eq_ref` classification and full recursive proof machinery) --
/// this needs to stay as cheap and non-committal as
/// `inner_closure_pap_value` is, since `closure_if_tree_value_at_literals`
/// calls it for whichever branch a concrete trace does *not* take, where
/// only the value (never a proof, never `g`'s own further resolution) is
/// needed; `resolve_closure_if_tree`'s own *taken*-branch case recurses
/// into `g`'s own full resolution separately, only when that branch is
/// actually reached.
pub(super) fn inner_closure_call_value(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    g: Hash,
    args: &[Hash],
    inner_params: &[Expr],
    inner_concrete: &[i64],
    inner_facts: &[Expr],
) -> Option<Expr> {
    let (g_arity, g_body, g_is_rec) = compile::peel(store, g)?;
    let g_captures = compile::free_vars(store, g_body, g_arity, g_is_rec);
    let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let call_fn = combinators.call_ref(g, &g_captures, &g_dummy)?;
    let g_env_denoted = if g_captures.is_empty() {
        None
    } else {
        let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
        let mk_env_expr = combinators.cp.mk_env_ref(&g_sig);
        let cd: Vec<Expr> = g_captures
            .iter()
            .map(|&rel| inner_params.get(rel as usize).cloned())
            .collect::<Option<Vec<_>>>()?;
        Some(apply_n(mk_env_expr, cd))
    };
    let inner_frame: Vec<Expr> = inner_params.to_vec();
    let mut arg_exprs = Vec::with_capacity(args.len());
    for &a in args {
        arg_exprs.push(denote(store, a, &combinators.cp.arith, &inner_frame)?);
    }
    let mut call_args = Vec::with_capacity(1 + arg_exprs.len());
    call_args.extend(g_env_denoted);
    call_args.extend(arg_exprs);
    let _ = (inner_concrete, inner_facts); // unused here -- no proof is built, only the value
    Some(apply_n(call_fn, call_args))
}

/// The literal value of `tree`'s own subtree, at `root`'s own literal
/// inner frame (`inner_params`/`inner_concrete`/`inner_facts`) -- no
/// proof, just the `Expr` matching whatever `clo_eq_ref_if_tree`'s own
/// axiom RHS-formula would produce for this subtree once substituted at
/// these same literals. Used for whichever branch a concrete trace does
/// *not* take (still needed, since `ite_clo(dc, dt, de)` needs both
/// `dt`/`de` present syntactically) -- `resolve_closure_if_tree` builds
/// the *taken* branch's own value (and a proof chaining it to a concrete
/// leaf) itself, more expensively, since only that one ever needs it.
#[allow(clippy::too_many_arguments)]
pub(super) fn closure_if_tree_value_at_literals(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    tree: &DecisionTree,
    leaf_shapes: &HashMap<Hash, ClosureIfTreeLeafShape>,
    inner_params: &[Expr],
    inner_concrete: &[i64],
    inner_facts: &[Expr],
    k: usize,
) -> Option<Expr> {
    match tree {
        DecisionTree::Leaf(h) => match leaf_shapes.get(h)? {
            ClosureIfTreeLeafShape::Abs { .. } => {
                let (v, _caps) = inner_closure_literal_value(combinators, *h, inner_params, inner_concrete, inner_facts)?;
                Some(v)
            }
            ClosureIfTreeLeafShape::Pap { g, args } => {
                let (v, _g_caps, _supplied) = inner_closure_pap_value(store, combinators, *g, args, inner_params, inner_concrete, inner_facts)?;
                Some(v)
            }
            ClosureIfTreeLeafShape::Call { g, args } => inner_closure_call_value(store, combinators, *g, args, inner_params, inner_concrete, inner_facts),
        },
        DecisionTree::If { cond, then_branch, else_branch } => {
            let params_full: Vec<Expr> = inner_params.to_vec();
            let dc = denote(store, *cond, &combinators.cp.arith, &params_full)?;
            let dt = closure_if_tree_value_at_literals(store, combinators, then_branch, leaf_shapes, inner_params, inner_concrete, inner_facts, k)?;
            let de = closure_if_tree_value_at_literals(store, combinators, else_branch, leaf_shapes, inner_params, inner_concrete, inner_facts, k)?;
            let ite_clo = combinators.cp.ite_clo_ref(k);
            Some(kernel::app3(ite_clo, dc, dt, de))
        }
    }
}

/// Recursively walks `tree`, concretely resolving `cond` at each internal
/// node (via `eval_and_prove`, following whichever branch it takes) until
/// reaching a leaf. Returns the reached leaf's own callee `Hash` (the
/// leaf itself for `Abs`, `g` for `Pap`), its own captures resolved to
/// literal triples, its own supplied-args triples (empty for `Abs`, whose
/// own callee is already exactly `k`-ary; `g`'s own supplied args for
/// `Pap`, prepended to the outer over-application's own extra args by
/// `resolve_closure_shape_to_leaf` -- `Pap`'s own convention), this
/// *subtree*'s own literal value (the same formula
/// `closure_if_tree_value_at_literals` would give for it, needed so the
/// caller one level up can build `ite_clo(dc, dt, de)` around it), the
/// reached leaf's own literal value, and a proof that the subtree's value
/// equals the leaf's -- chained one `ite_clo_eq_ref` step per internal
/// node on the path actually taken, generalizing
/// `eval_and_prove_call_over`'s own original single-step version (still
/// exactly what this produces for a depth-1, all-`Abs` tree).
///
/// What the reached leaf resolves to: either a genuine `Abs`/`Pap` value
/// (`Direct`, still needing the caller's own `apply_clo_eq_ref`/
/// `apply_pap_eq_ref` dispatch -- the only case before `Call`-shaped
/// leaves were supported), or a `Call`-shaped leaf whose own further
/// indirection has *already* been fully resolved, via a recursive
/// `resolve_closure_shape_to_leaf` call mirroring the root-level `Call`
/// arm exactly, down to a genuine literal-lambda leaf and a complete
/// "call with all args" fact (`Indirect` -- the caller must reuse
/// `apply_eq_chosen` as-is, never build its own). The `Indirect` variant's
/// three facts can be threaded up through however many further `If`
/// levels sit above the leaf that produced them with no special care,
/// same as `ValueTriples`' own embedded fields.
pub(super) enum IfTreeLeafResolution {
    Direct {
        chosen: Hash,
        cap_triples: ValueTriples,
        arg_prefix: ValueTriples,
    },
    Indirect {
        chosen: Hash,
        chosen_cap_triples: ValueTriples,
        chosen_arg_triples: ValueTriples,
        /// `: Id(clo_ty(k), <this leaf's own canonical value>, chosen_value)`.
        leaf_to_chosen: Expr,
        chosen_value: Expr,
        apply_eq_chosen: Expr,
    },
}

#[allow(clippy::type_complexity, clippy::too_many_arguments)]
pub(super) fn resolve_closure_if_tree(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    tree: &DecisionTree,
    leaf_shapes: &HashMap<Hash, ClosureIfTreeLeafShape>,
    inner_params: &[Expr],
    inner_concrete: &[i64],
    inner_facts: &[Expr],
    k: usize,
    extra_arg_triples: &[(i64, Expr, Expr)],
) -> Option<(IfTreeLeafResolution, Expr, Expr, Expr)> {
    match tree {
        DecisionTree::Leaf(h) => match leaf_shapes.get(h)? {
            ClosureIfTreeLeafShape::Abs { .. } => {
                let (value_lit, cap_triples) = inner_closure_literal_value(combinators, *h, inner_params, inner_concrete, inner_facts)?;
                let proof = kernel::refl(value_lit.clone());
                Some((IfTreeLeafResolution::Direct { chosen: *h, cap_triples, arg_prefix: Vec::new() }, value_lit.clone(), value_lit, proof))
            }
            ClosureIfTreeLeafShape::Pap { g, args } => {
                let (value_lit, g_cap_triples, supplied_triples) =
                    inner_closure_pap_value(store, combinators, *g, args, inner_params, inner_concrete, inner_facts)?;
                let proof = kernel::refl(value_lit.clone());
                Some((
                    IfTreeLeafResolution::Direct { chosen: *g, cap_triples: g_cap_triples, arg_prefix: supplied_triples },
                    value_lit.clone(),
                    value_lit,
                    proof,
                ))
            }
            ClosureIfTreeLeafShape::Call { g, args } => {
                let mut g_arg_triples = Vec::with_capacity(args.len());
                for &a in args {
                    let (x, d, p) = eval_and_prove(store, a, combinators, inner_params, inner_concrete, inner_facts)?;
                    g_arg_triples.push((x, d, p));
                }
                // `leaf_value` (this leaf's own canonical value) matches
                // `closure_leaf_call_value_expr`'s own axiom-side
                // construction exactly (both `call_ref(g)` applied to the
                // same denoted args over the same frame): reused directly
                // from `build_clo_call_bridge`'s own first return value
                // rather than rebuilt, avoiding redundant work.
                let (leaf_value, g_call_at_lit_env_lit_args, g_bridge, g_axiom_at_literals, g_inner_params, g_inner_concrete, g_inner_facts, g_k, g_shape) =
                    build_clo_call_bridge(store, combinators, *g, &g_arg_triples, inner_params, inner_concrete, inner_facts)?;
                if g_k != k {
                    return None; // should be unreachable given classify_closure_if_tree_leaf's own validation, but stay defensive
                }

                // Recurse into `g`'s own further resolution -- the same
                // machinery `ClosureRhsShape::Call`'s own root-level arm
                // uses, needing the *same* `extra_arg_triples` the
                // enclosing over-application ultimately supplies (there is
                // only ever one final `apply_*_eq_ref` step in the whole
                // chain, applied once a genuine `Abs`/`Pap` leaf is finally
                // reached, however many further `Call`/`IfTree`/`Pap`
                // layers sit in between).
                let (chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, leaf_to_chosen, apply_eq_chosen) = resolve_closure_shape_to_leaf(
                    store,
                    combinators,
                    &leaf_value.clone(),
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

                let full_proof = kernel::refl(leaf_value.clone());
                let resolution = IfTreeLeafResolution::Indirect {
                    chosen,
                    chosen_cap_triples,
                    chosen_arg_triples,
                    leaf_to_chosen,
                    chosen_value,
                    apply_eq_chosen,
                };
                Some((resolution, leaf_value.clone(), leaf_value, full_proof))
            }
        },
        DecisionTree::If { cond, then_branch, else_branch } => {
            let (result_c, denote_c, proof_c) = eval_and_prove(store, *cond, combinators, inner_params, inner_concrete, inner_facts)?;

            let (taken, other) = if result_c != 0 { (then_branch, else_branch) } else { (else_branch, then_branch) };
            let (resolution, taken_subtree_value, leaf_value, taken_proof) =
                resolve_closure_if_tree(store, combinators, taken, leaf_shapes, inner_params, inner_concrete, inner_facts, k, extra_arg_triples)?;
            let other_value = closure_if_tree_value_at_literals(store, combinators, other, leaf_shapes, inner_params, inner_concrete, inner_facts, k)?;

            combinators.cp.arith.lit(result_c);
            let ite_eq_axiom = combinators.ite_clo_eq_ref(result_c, k);

            let lit_xc = combinators.cp.arith.lit_ref(result_c);
            let ite_clo = combinators.cp.ite_clo_ref(k);
            let int_ty = combinators.cp.arith.int_ty();
            let clo_ty = combinators.cp.clo_ty(k);

            let (dt, de) = if result_c != 0 {
                (taken_subtree_value.clone(), other_value.clone())
            } else {
                (other_value.clone(), taken_subtree_value.clone())
            };

            // `ite_clo_eq_ref`'s own bridge: first, `cong1` over
            // `ite_clo_k`'s own first (`Int`) argument (`dt`/`de` held
            // fixed at their literal values), turning `denote(cond,lits)`
            // into `lit_ref(xc)`; then the axiom itself, instantiated at
            // the two branches' own literal values -- see
            // `ite_clo_eq_ref`'s own docs for why both steps are needed.
            let f_cond_body = kernel::app3(kernel::shift(&ite_clo, 0, 1), kernel::var(0), kernel::shift(&dt, 0, 1), kernel::shift(&de, 0, 1));
            let f_cond = kernel::lam(int_ty.clone(), f_cond_body);
            let cong_cond = kernel::cong1(&int_ty, &clo_ty, &f_cond, denote_c.clone(), lit_xc.clone(), proof_c);
            let this_subtree_value = kernel::app3(ite_clo.clone(), denote_c, dt.clone(), de.clone());
            let ite_at_lit_xc = kernel::app3(ite_clo, lit_xc, dt.clone(), de.clone());

            let ite_axiom_at = apply_n(ite_eq_axiom, vec![dt, de]);
            let branch_bridge = kernel::trans_proof(&clo_ty, &this_subtree_value, &ite_at_lit_xc, &taken_subtree_value, cong_cond, ite_axiom_at);
            let full_proof = kernel::trans_proof(&clo_ty, &this_subtree_value, &taken_subtree_value, &leaf_value, branch_bridge, taken_proof);

            Some((resolution, this_subtree_value, leaf_value, full_proof))
        }
    }
}

/// The `Clo_k`/`Int` signature of a capture list, relative to the *calling*
/// scope's own `param_types` -- `sig[i]` is `Some(k)` iff `captures[i]`
/// resolves to a `Clo_k`-typed value there, `None` for an `Int`-typed one.
/// `Env`/`mk_env` are keyed by this signature rather than by
/// `captures.len()` alone, the same way
/// `call_ref`/`pap_ref` already vary their own call-argument types by
/// `param_types` at each position: two combinators that happen to
/// capture the same *number* of values still share one `Env` postulate
/// as long as the *types* also match (the common, all-`Int` case), and
/// only a genuinely mixed signature gets its own. `None` if any `rel` is
/// out of range for `caller_param_types` -- `build_env_expr`'s own
/// section docs above explain why that's never actually expected to
/// happen (every capture is relative to exactly the ambient scope
/// `caller_param_types` describes), but this stays a clean rejection
/// rather than a panic if it somehow did.
pub(super) fn capture_sig(captures: &[u32], caller_param_types: &[Option<usize>]) -> Option<Vec<Option<usize>>> {
    captures.iter().map(|&rel| caller_param_types.get(rel as usize).copied()).collect()
}

/// Builds `mk_env(v_1,...,v_n)` for a combinator whose relative capture
/// indices are `captures` (`compile::free_vars`), reading each captured
/// value's *current* value out of the *calling* function's own
/// `(params, param_types)` frame -- mirroring `lower_wat.rs`'s
/// `push_closure_env`, but resolving each slot directly against `params`
/// rather than through a `build_read`-style recursive lookup (see
/// `build_env_expr`'s own section docs above for why that recursive case
/// never actually arises here). Each captured index must resolve
/// directly to one of the caller's own parameters (`rel < params.len()`)
/// -- but may be `Clo`-typed or `Int`-typed freely; `capture_sig` picks
/// out which, and `Env`/`mk_env` are keyed by that signature rather than
/// assuming every capture is `Int`.
pub(super) fn build_env_expr(combinators: &mut ClosureCombinators, captures: &[u32], params: &[Expr], param_types: &[Option<usize>]) -> Option<Expr> {
    let sig = capture_sig(captures, param_types)?;
    let mut values = Vec::with_capacity(captures.len());
    for &rel in captures {
        let v = params.get(rel as usize)?.clone();
        values.push(v);
    }
    let mk_env = combinators.cp.mk_env_ref(&sig);
    Some(apply_n(mk_env, values))
}

/// Like `collect_literals`, but for the closures fragment: an `App` chain
/// is only ever a closure call (resolved the same way `denote_closure`
/// resolves one), never rejected outright the way `collect_literals`
/// (built for the arithmetic-only fragments) rejects any bare `App`.
/// `param_types[i]` is `Some(k)` for a closure-typed parameter (see
/// `denote_closure`'s docs), `None` for a plain `Int` one.
pub(super) fn collect_literals_closure(store: &TermStore, h: Hash, param_types: &[Option<usize>], out: &mut Vec<i64>) -> bool {
    let all = |hs: &[Hash], out: &mut Vec<i64>| hs.iter().all(|&a| collect_literals_closure(store, a, param_types, out));
    match compile::classify(store, h, param_types.len(), None) {
        Shape::VarCall { var, args, .. } => param_types.get(var as usize).copied().flatten().is_some() && all(&args, out),
        Shape::CombinatorCall { args, .. } => all(&args, out),
        Shape::SelfCall(_) | Shape::OtherCall => false,
        Shape::Var(_) => true,
        Shape::Lit(n) => {
            if !out.contains(&n) {
                out.push(n);
            }
            true
        }
        Shape::Prim(_, a, b) => all(&[a, b], out),
        Shape::If(c, t, e) => all(&[c, t, e], out),
        Shape::Combinator { .. } => true, // a bare value -- opaque, nothing inside it to collect
    }
}

/// Translates a closures-fragment term into a kernel expression -- see the
/// section docs above for what each case represents on both readings.
/// `params[i]`/`param_types[i]` describe the enclosing function's own
/// `Var(i)`: `param_types[i] = Some(k)` for a closure-typed parameter
/// always called with `k` arguments (`compile::infer_closure_arities`'s own
/// classification, reindexed from its positional convention to `denote`'s
/// by-`Var`-index one), `None` for a plain `Int` parameter. `params` are
/// the parameters' postulates as `Const`s, which no later push shifts.
pub(super) fn denote_closure(
    store: &TermStore,
    h: Hash,
    combinators: &mut ClosureCombinators,
    params: &[Expr],
    param_types: &[Option<usize>],
) -> Option<Denoted> {
    denote_closure_typed(store, h, None, param_types, combinators, params)
}

/// Attempts to build an [`EquivalenceProof`] for `h`, covering every input,
/// for the closures fragment `compile.rs` compiles, capturing, partially
/// applied, self-recursive-combinator-calling, or none of those (see the
/// section docs above for exactly what's in and out of scope). Returns
/// `None` for anything outside it: `h` *itself* `Rec`-wrapped (proving a
/// self-recursive function's own body is `build_universal`'s job, not
/// this one's -- a combinator it calls or uses as a value may still be
/// self-recursive), an application whose callee is neither a closure-typed
/// parameter nor a literal lambda/named recursive combinator, an
/// inconsistent arity for a closure-typed parameter, an over-application
/// of a literal lambda or recursive combinator whose own saturated result
/// doesn't itself denote `Clo` (see `combinator_return_type`; a `Clo`-
/// returning one is covered, dispatched directly on the extra
/// arguments), an `If` whose branches aren't both `Int` or both `Clo` (or
/// one of each), a captured value (for a capturing combinator) that
/// doesn't resolve directly to one of the calling function's own
/// parameters (freely `Int`- or `Clo`-typed -- see `build_env_expr`'s own
/// docs), or a partial application (fewer arguments than arity) whose
/// root itself captures anything or is itself self-recursive. A
/// whole-function result may be `Int` *or* `Clo_k` (e.g. `\x. \y. x+y`
/// used bare, or a term ending in a bare closure-typed parameter read) --
/// `result_ty` on the returned proof is `Int`'s or that `Clo_k`'s own
/// postulate accordingly, never hardcoded.
pub fn prove_closure_expr(store: &TermStore, h: Hash) -> Option<EquivalenceProof> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    if is_rec {
        return None;
    }

    let found = compile::infer_closure_arities(store, body, arity, None)?;
    // See `param_types_for`'s own docs: an inconsistently-called `Var` is
    // declined the same way an absent one already is.
    let param_types: Vec<Option<usize>> = (0..arity as u32)
        .map(|i| match found.get(&i) {
            Some(compile::ArityUse::Consistent(k)) => Some(*k),
            Some(compile::ArityUse::Inconsistent) | None => None,
        })
        .collect();

    let mut lits = Vec::new();
    if !collect_literals_closure(store, body, &param_types, &mut lits) {
        return None;
    }

    let mut combinators = ClosureCombinators::new(store);
    for n in lits {
        combinators.cp.arith.lit(n);
    }

    let mut params = Vec::with_capacity(arity);
    for &ty in &param_types {
        let pos = match ty {
            Some(k) => {
                let clo_ty = combinators.cp.clo_ty(k);
                combinators.cp.arith.p.push(clo_ty)
            }
            None => {
                let int_ty = combinators.cp.arith.int_ty();
                combinators.cp.arith.p.push(int_ty)
            }
        };
        params.push(combinators.cp.arith.p.get(pos));
    }

    let denoted = denote_closure(store, body, &mut combinators, &params, &param_types)?;
    // `result_ty` mirrors `denoted`'s own tag: `Int`'s postulate for a
    // `Denoted::Int`, or the specific `Clo_k` for a `Denoted::Clo` --
    // `k` re-derived structurally via `return_type_of` applied to the
    // whole body (no self-call concept at this top level, so `self_idx`
    // is `None`, same as the nested-`If` case in `denote_closure` itself),
    // kept in lockstep with every `Denoted::Clo`-producing shape
    // `denote_closure` recognizes -- see `return_type_of`'s own docs.
    // `clo_ty` is pure and never pushes, so calling it again here (after
    // `denote_closure` already called it for this exact `k` while
    // building `denoted`, to type its own `debug_assert_has_type` checks)
    // is cheap, not a fresh postulate.
    let (result_ty, denotation) = match denoted {
        Denoted::Int(e) => (combinators.cp.arith.int_ty(), e),
        Denoted::Clo(e) => {
            let k = return_type_of(store, body, arity, None, &param_types).flatten()?;
            (combinators.cp.clo_ty(k), e)
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
