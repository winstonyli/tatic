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
// anything concrete, so no per-value grounding is needed.
//
// Scope, honestly: the *main*, top-level term must still be non-recursive
// (`prove_closure_expr`'s own top-level check) -- proving what a
// self-recursive function's *own* body computes is `prove_tail_recursive_universal`'s
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
// `denote_closure` never enter a registered combinator's own body
// (a call is always postulated opaque), and `compile::peel` always folds
// consecutive `Abs` layers into one combinator before that combinator is
// ever registered, so there is no way for this fragment to encounter one
// combinator's own literal-lambda body containing *another*, separately
// registered one -- every capture list `build_env_expr` is ever asked to
// resolve is relative to the one flat ambient scope currently being
// denoted (the top-level term's own parameters, or `prove_tail_recursive_universal`'s
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
// (`prove_tail_recursive_universal`'s own fragment already relied on that). `pap_ref` now
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
/// classification when given `self_idx` (same as `prove_tail_recursive_universal`'s own
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
/// that case independently).
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
/// `denote_closure`'s own nested-`If`
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
}

/// Lets code holding a `&(mut) ClosurePostulates` -- `prove_tail_recursive_universal`'s own
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
        let mut ty = int_ty;
        for _ in 0..arity {
            ty = kernel::arrow(int_ty, ty);
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
    /// open-ended arithmetic domain, never given a
    /// case-elimination principle), so there's no way to build this from
    /// anything already postulated (see `RELATED_WORK.md` section 11's own
    /// correction). Called directly by whichever site needs it.
    pub(super) fn ite_clo_ref(&mut self, arity: usize) -> Expr {
        if let Some(&pos) = self.ite_clo_pos.get(&arity) {
            return self.arith.p.get(pos);
        }
        let clo_ty = self.curried_int_ty(arity);
        let ite_ty = kernel::arrow(self.arith.int_ty(), kernel::arrow(clo_ty, kernel::arrow(clo_ty, clo_ty)));
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
        let mut ty = env_ty;
        // Fold from the *last* capture outward, so the final iteration
        // (sig[0]) ends up as the outermost/first-applied parameter,
        // matching `apply_n`'s left-to-right application order (the same
        // convention `call_ref`'s own loop documents).
        for dom in doms.iter().rev() {
            ty = kernel::arrow(*dom, ty);
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
        let ty = kernel::arrow(env_ty, clo_ty);
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
/// (`prove_tail_recursive_universal`'s own pipeline, once it needs to create a closure
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
        let mut ty = ret;
        // Var(0) is last-applied (innermost -- wrap it first, so the
        // final iteration, Var(arity-1) = first-applied, ends up
        // outermost, matching apply_n's left-to-right application order).
        for dom in &doms {
            ty = kernel::arrow(*dom, ty);
        }
        if let Some(env_ty) = env_ty {
            ty = kernel::arrow(env_ty, ty);
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
        let mut ty = ret;
        for dom in &doms {
            ty = kernel::arrow(*dom, ty);
        }
        if let Some(env_ty) = env_ty {
            ty = kernel::arrow(env_ty, ty);
        }
        let pos = self.cp.arith.p.push(ty);
        self.cp.pap_pos.insert((h, k), pos);
        Some(self.cp.arith.p.get(pos))
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
        let v = *params.get(rel as usize)?;
        values.push(v);
    }
    let mk_env = combinators.cp.mk_env_ref(&sig);
    Some(apply_n(mk_env, values))
}

/// Attempts to build an [`EquivalenceProof`] for `h`, covering every input,
/// for the closures fragment `compile.rs` compiles, capturing, partially
/// applied, self-recursive-combinator-calling, or none of those (see the
/// section docs above for exactly what's in and out of scope). Returns
/// `None` for anything outside it: `h` *itself* `Rec`-wrapped (proving a
/// self-recursive function's own body is `prove_tail_recursive_universal`'s job, not
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
    if !collect_literals(store, body, &LitScope::Closure { arity, self_idx: None, param_types: &param_types }, &mut lits) {
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

    let denoted = denote_closure(body, &mut SelfCalls::None, &param_types, &mut combinators, &params)?;
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
    let proof = kernel::refl(denotation);
    let proof_ty = kernel::id(result_ty, denotation, denotation);
    combinators.cp.arith.p.check(&proof, &proof_ty).ok()?;

    Some(EquivalenceProof {
        globals: combinators.cp.arith.p.globals,
        arity,
        result_ty,
        denotation,
        proof,
    })
}
