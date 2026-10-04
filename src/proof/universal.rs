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
// (`denote_with_placeholders`); `ev_leaf_i` is `Ev`'s constructor for this
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
// `Clo`-typed values (`find_self_calls`/`denote_with_placeholders` both
// recurse into one, embedding it opaquely via `ite_ref`/`ite_clo_ref`,
// same as `denote_closure` always has). `prove_tail_recursive_call`
// already handles arbitrary branching
// *and* arbitrary self-call placement on its own (it just follows one
// concrete path through the tree per call, denoting whatever it finds
// along the way), so neither of those needed widening.
//
// `build_universal` also covers a *closure-typed parameter*, threaded
// through the recursion unchanged or called via ordinary `App` (`Clo_k`,
// see `ClosurePostulates::clo_ty`, is a literal `Int -> .. -> Int` kernel
// Pi type, not an opaque postulate, so calling one needs no axiom at all)
// within a leaf or a self-call argument (`param_types`, the same
// `Var`-index-keyed classification `denote_closure`'s own fragment uses,
// computed once via `compile::infer_closure_arities` on the whole body
// including self-call sites) -- e.g. "iterate a closure `n` times": `rec f
// n g x = if n<=0 then x else f(n-1, g, g(x))`. This part needs only
// `ClosurePostulates::clo_ty`, reused directly (`ClosurePostulates:
// Deref<Target = ArithPostulates>` lets this whole pipeline keep calling
// every plain-arithmetic postulate method unchanged). A closure-typed
// self-call argument, or one fed to a closure call, may also be a freshly
// *created* closure (`denote_closure_typed` mirrors `denote_closure`'s own
// `Term::Abs`/`Term::Rec` handling via the same `ClosureCombinators`), not
// just a bare parameter reference, and an `If` choosing between two
// `Clo`-typed values is in scope too (`ite_clo_ref`, same as
// `denote_closure`'s own) -- see `build_universal`'s own doc comment below
// for the one thing still out of scope here (a captured free variable).
// `params_and_close_typed`'s scope locals are `Free`s (`RELATED_WORK.md`
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
// compiled but never proven. `denote_closure_typed` (the self-call-argument
// denotation `new_params_for` uses) mirrors `denote_closure`'s own
// `Term::Abs`/`Term::Rec` handling almost verbatim, now that `arith` is a
// full `ClosureCombinators` (not just `ClosurePostulates`) -- registering a
// combinator, calling one directly, or partially applying one (still never
// a *recursive* root, per `pap_ref`'s own restriction) all reuse the exact
// same methods `prove_closure_expr` does. A leaf's own *top-level*
// expression gets the identical treatment: `denote_with_placeholders`
// (the placeholder-substitution-aware sibling `combine_i`'s body uses)
// and `find_self_calls` (which recurses into a closure call's own
// arguments, or treats a bare closure value as opaque, the same way
// `collect_literals` already does) mirror `denote_closure_typed`'s/
// `denote_closure`'s handling too -- e.g. `(\y. n+y)(5) + f(n-1)`, a
// closure-call's result combined arithmetically with the recursive call
// directly, not nested inside any self-call's own argument list.
// `register`/`call_ref`/`pap_ref`, and transitively `mk_env_ref`/`env_ty`
// for a capturing one, are all lazily memoized; either `denote_closure_typed`'s
// or `denote_with_placeholders`'s first real call (from inside a temporary
// scope) may trigger any of them for the first time. Also honestly scoped: `eval_and_prove`/
// `build_ev_witness` (the *instance*, per-call specialization) remain
// untouched and still reject `App`/`Abs` outright, so a concrete instance
// proof for either shape still declines -- `kernel_verified` doesn't
// depend on that (see `jit.rs`'s own docs), so this doesn't weaken what
// actually gets verified, only what gets additional, call-specific
// evidence.

/// `f` applied to each of `args` in order (left to right).
pub(super) fn apply_n(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, kernel::app)
}

/// `Ev(params, v) : Sort(0)` -- `ev_pos`'s postulate (see `build_universal`)
/// applied to `params` then `v`, via `arith.p.get`. A free function (not
/// just `build_universal`'s own local closure) so `build_ev_witness`'s
/// branching-leaf recasting can build the same `Ev(...)` application it
/// does, rather than reimplementing it.
pub(super) fn ev_of(arith: &ArithPostulates, ev_pos: usize, params: &[Expr], v: Expr) -> Expr {
    apply_n(arith.p.get(ev_pos), params.iter().cloned().chain([v]))
}
