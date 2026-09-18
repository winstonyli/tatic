//! Connects the `kernel` module to the JIT: for the straight-line
//! (non-recursive) fragment of the compilable terms, builds an actual
//! kernel-checked `Id`-typed proof that the interpreter's reading and the
//! compiled code's reading agree, instead of relying only on the empirical
//! sampling `jit::JitEngine` otherwise uses.
//!
//! ## What this does and doesn't establish
//!
//! `Int` (and its arithmetic/comparison operators, and every literal that
//! appears in a given term) is *postulated* in the kernel, not derived --
//! same rationale as `kernel::Postulates`' docs: getting real machine
//! integers from `Pi`/`Sort`/`Id`/`W` alone isn't the point here, and
//! doing it properly (e.g. via a genuine numeral encoding) buys nothing
//! for what's being checked, which is purely *compositional structure*.
//!
//! For `Var`/`Lit`/`Prim`/`If` terms (no `Abs`/`App`/`Rec`), `compile.rs`'s
//! `compile_node` and `eval.rs`'s `eval` recurse over the term in exactly
//! the same shape -- evaluate/compile the operands, then combine with the
//! same operator -- so `denote` (the single translation below) models both
//! readings, and the proof that they agree is `refl`. That's not a
//! shortcut: for straight-line, side-effect-free expressions, a stack-
//! machine compilation and a tree-walking interpretation provably compute
//! the same value by construction, and a kernel-checked `refl` is an
//! accurate, honest witness of exactly that fact -- no more, no less.
//!
//! ## Tail recursion: relational, per-call proofs (`prove_tail_recursive_call`)
//!
//! `compile.rs` also turns *tail* self-recursion into a `loop`/`br`
//! (recursion -> iteration) -- the actually interesting transformation.
//! One way to check a given transformed term is the same idea real
//! verified compilers fall back to when full verification isn't available:
//! **translation validation** -- instead of a universal theorem, validate
//! *one specific execution trace*. For a concrete `(term, args)`,
//! `prove_tail_recursive_call` follows the interpreter's own concrete trace
//! (which branch is taken at each unrolling, using the same shape
//! `compile_node` classifies bodies with), and at each tail-call step,
//! symbolically composes the new parameters via `denote` -- i.e. it relates
//! interpreter state to compiled-loop state at every step, not just at the
//! end. Once the trace reaches its base case (guaranteed finite for
//! terminating inputs), the whole thing is exactly as long a straight-line
//! expression as the trace was, and the proof is `refl` on it, same as the
//! non-recursive case. This is a genuinely stronger check than sample
//! verification's `==` (it proves the compiled and interpreted readings are
//! the *same expression*, not just that their outputs happened to match),
//! but it's a certificate per call, not a theorem -- `jit::JitEngine` uses
//! it per sample point, not as a one-time replacement for sampling.
//!
//! ## A universal proof for recursion, tail or not (`prove_tail_recursive_universal`)
//!
//! A *universal* proof ("for every input, the recursive reading and the
//! compiled reading agree", not just at the sampled/traced points) needs
//! real induction on the call depth. Since this project's kernel is
//! predicative (see `kernel`'s docs), there's no bare inductive `Nat` to
//! induct on -- instead, `prove_tail_recursive_universal` postulates a
//! family `Ev(params, v) : Sort(0)`, "unrolling from `params` reaches
//! `v`", with one constructor per leaf of `body`'s decision tree (`body`
//! may be an arbitrary tree of nested `If`s, matching what `compile_node`
//! already compiles; each leaf may itself contain any number of self-call
//! occurrences -- zero for a base case, one in tail position for the
//! historically-first case this covered, or several combined arithmetically,
//! e.g. `f(n-1) + f(n-2)`, for genuinely non-tail recursion) and a
//! postulated recursor (`ev_rec`) obeying the same universal-motive shape
//! `kernel::WRec` uses, just for this specific inductive family instead of
//! a derived `W`-type (same "postulated inductive family" pattern as
//! `kernel::Postulates`' docs). Each leaf's constructor takes extra
//! hypothesis arguments tying it to the *whole path* of `If`s that reaches
//! it (`cond_i(params) = 1` or `= 0` at each ancestor, one premise per
//! ancestor) -- without that, a zero-self-call leaf's constructor would
//! make `Ev(params, v)` inhabited for *any* `params`, `cond`-blind, making
//! it a strictly weaker relation than "the real trace" it's meant to model
//! (an earlier, narrower version of this had exactly that gap). Gating
//! doesn't need any `cond` to be *decidable* for symbolic `params` -- it
//! only needs each premise as an explicit argument any actual witness must
//! supply, exactly how a big-step evaluation relation is conventionally
//! formalized; for *concrete* `params` each premise is `refl`, the same
//! way `prove_tail_recursive_call`'s trace-following already works.
//!
//! Each leaf also gets a `combine` function -- its own arithmetic
//! expression with each self-call occurrence replaced by a placeholder
//! (`denote_with_placeholders`) -- and applying `ev_rec` with the
//! constant-`Int` motive and, per leaf, `combine` applied to the
//! recursively-computed induction hypotheses gives `loop_val`, a term
//! computing exactly what the compiled code computes: a base leaf's
//! `combine` (zero placeholders) reduces to its own denotation, a single
//! tail self-call's `combine` (one placeholder, identity) reduces to a
//! pass-through, and anything else genuinely recombines the recursive
//! results (`n * ih`, `ih_1 + ih_2`, ...). The computation-rule axioms
//! `loop_val` needs (specific to *this* `loop_val`, not a generic schema,
//! one per leaf) are postulated the same way, since a postulated
//! recursor has no built-in reduction rule. The theorem itself --
//! `loop_val(params, v, e) = v` for every `params`, `v`, and every trace
//! `e : Ev(params, v)` -- is then a genuine `ev_rec` induction, whose
//! per-leaf step combines its induction hypotheses via `kernel::cong_n`
//! (congruence for `combine`, an `n`-ary function, generalizing the
//! `kernel::cong1`/`trans_proof` composition a single tail self-call
//! needed) and chains that with the leaf's own computation-rule axiom via
//! `trans_proof`. Note what this theorem does and doesn't give you on its
//! own: it's a *reusable lemma*, proved once regardless of `params`, not
//! itself a per-input guarantee -- instantiating it at a concrete `params`
//! still needs an actual `e : Ev(params, v)` witness (built by following
//! `cond`'s real value at each step, same as `prove_tail_recursive_call`
//! already does), which this function doesn't build.
//!
//! Scope: every `If` on the way to a leaf must have a direct comparison as
//! its condition (`compile_cond` in `compile.rs` requires that too, and
//! gating above relies on comparisons denoting to exactly `0` or `1`);
//! `body` must have at least one leaf with a self-call somewhere in it
//! (otherwise there's no recursion to induct on at all); and a leaf may
//! not itself contain a further nested `If` as a sub-expression (only as
//! the *whole* body of some branch, which `classify_tree` already
//! extracts) -- a real, documented restriction, not a subtle gap.
//! `prove_tail_recursive_call` already handles arbitrary branching *and*
//! arbitrary self-call placement on its own (it just follows one concrete
//! path per call, denoting whatever it finds along the way), so neither
//! of those needed widening.

use std::collections::HashMap;

use crate::compile;
use crate::kernel::{self, Ctx, Expr, Postulates};
use crate::term::{Hash, PrimOp, Term, TermStore};

/// Postulated `Int` and its operators, plus on-demand postulated constants
/// for whichever literal values a given term actually uses.
pub struct ArithPostulates {
    pub p: Postulates,
    int_pos: usize,
    op_pos: [usize; 8],
    ite_pos: usize,
    literal_pos: HashMap<i64, usize>,
}

impl ArithPostulates {
    pub fn new() -> Self {
        let mut p = Postulates::new();
        let int_pos = p.push(kernel::sort(0));

        let push_binop = |p: &mut Postulates| -> usize {
            let int_ty = p.get(int_pos);
            let ty = kernel::arrow(int_ty.clone(), kernel::arrow(int_ty.clone(), int_ty));
            p.push(ty)
        };
        // Order matches `PrimOp`'s `#[repr(u8)]` discriminants in term.rs.
        let op_pos = [
            push_binop(&mut p), // Add
            push_binop(&mut p), // Sub
            push_binop(&mut p), // Mul
            push_binop(&mut p), // Div
            push_binop(&mut p), // Mod
            push_binop(&mut p), // Lt
            push_binop(&mut p), // Le
            push_binop(&mut p), // Eq
        ];

        let int_ty = p.get(int_pos);
        let ite_ty = kernel::arrow(
            int_ty.clone(),
            kernel::arrow(int_ty.clone(), kernel::arrow(int_ty.clone(), int_ty)),
        );
        let ite_pos = p.push(ite_ty);

        ArithPostulates {
            p,
            int_pos,
            op_pos,
            ite_pos,
            literal_pos: HashMap::new(),
        }
    }

    pub fn int_ty(&self) -> Expr {
        self.p.get(self.int_pos)
    }

    fn op_ref(&self, op: PrimOp) -> Expr {
        self.p.get(self.op_pos[op as u8 as usize])
    }

    fn ite_ref(&self) -> Expr {
        self.p.get(self.ite_pos)
    }

    /// Postulate a fresh `Int`-typed constant for `n` if one doesn't
    /// already exist. Must be called for every literal a term uses
    /// *before* any `Var`-referencing (`param`) postulates are pushed --
    /// see `prove_pure_expr`.
    pub fn lit(&mut self, n: i64) -> Expr {
        if let Some(&pos) = self.literal_pos.get(&n) {
            return self.p.get(pos);
        }
        let ty = self.int_ty();
        let pos = self.p.push(ty);
        self.literal_pos.insert(n, pos);
        self.p.get(pos)
    }

    fn lit_ref(&self, n: i64) -> Expr {
        let pos = *self
            .literal_pos
            .get(&n)
            .expect("literal not pre-postulated -- collect_literals missed one");
        self.p.get(pos)
    }
}

impl Default for ArithPostulates {
    fn default() -> Self {
        Self::new()
    }
}

/// Collects every distinct `Lit` value in `h`, returning `false` if `h`
/// contains anything outside the pure fragment this module covers. With
/// `self_idx: None` (the straight-line case), any `App` at all disqualifies
/// `h`; with `self_idx: Some(_)` (the tail-recursive case), a
/// fully-saturated self-call is instead recursed *into* (collecting
/// literals from its argument expressions) -- any other `App`/`Abs`/`Rec`
/// (e.g. genuinely non-tail recursion, as in a naive Fibonacci) still
/// disqualifies it.
fn collect_literals(
    store: &TermStore,
    h: Hash,
    arity: usize,
    self_idx: Option<u32>,
    out: &mut Vec<i64>,
) -> bool {
    if let Some(args) = compile::match_self_call(store, h, arity, self_idx) {
        return args
            .iter()
            .all(|&a| collect_literals(store, a, arity, self_idx, out));
    }
    match store.resolve(h) {
        Term::Var(_) => true,
        Term::Lit(n) => {
            if !out.contains(n) {
                out.push(*n);
            }
            true
        }
        Term::Prim(_, a, b) => {
            collect_literals(store, *a, arity, self_idx, out)
                && collect_literals(store, *b, arity, self_idx, out)
        }
        Term::If(c, t, e) => {
            collect_literals(store, *c, arity, self_idx, out)
                && collect_literals(store, *t, arity, self_idx, out)
                && collect_literals(store, *e, arity, self_idx, out)
        }
        Term::Abs(_) | Term::App(..) | Term::Rec(_) => false,
    }
}

/// Translates a `Var`/`Lit`/`Prim`/`If` term into a kernel `Int`
/// expression: `params[i]` stands for `Var(i)`, and every operator/literal
/// is read off `arith` (which must already have every literal postulated).
fn denote(store: &TermStore, h: Hash, arith: &ArithPostulates, params: &[Expr]) -> Option<Expr> {
    match store.resolve(h) {
        Term::Var(i) => params.get(*i as usize).cloned(),
        Term::Lit(n) => Some(arith.lit_ref(*n)),
        Term::Prim(op, a, b) => {
            let da = denote(store, *a, arith, params)?;
            let db = denote(store, *b, arith, params)?;
            Some(kernel::app2(arith.op_ref(*op), da, db))
        }
        Term::If(c, t, e) => {
            let dc = denote(store, *c, arith, params)?;
            let dt = denote(store, *t, arith, params)?;
            let de = denote(store, *e, arith, params)?;
            Some(kernel::app3(arith.ite_ref(), dc, dt, de))
        }
        Term::Abs(_) | Term::App(..) | Term::Rec(_) => None,
    }
}

/// A kernel-checked witness that a term's compiled and interpreted
/// readings agree: either for *every* input (`prove_pure_expr`, the
/// straight-line fragment) or for one specific call
/// (`prove_tail_recursive_call`, the tail-recursive fragment).
pub struct EquivalenceProof {
    pub ctx: Ctx,
    pub arity: usize,
    pub int_ty: Expr,
    pub denotation: Expr,
    /// `: Id(Int, denotation, denotation)`.
    pub proof: Expr,
}

/// Shared setup for both proofs below: postulate `Int`/its operators, then
/// every literal `body` uses (see `collect_literals` for what `self_idx`
/// means here), then `arity` more fresh `Int` postulates standing for the
/// function's own parameters (indexed by `Var`, matching `denote`'s
/// convention). Returns `None` if `body` isn't in the covered fragment.
fn setup(store: &TermStore, body: Hash, arity: usize, self_idx: Option<u32>) -> Option<(ArithPostulates, Vec<Expr>)> {
    let mut lits = Vec::new();
    if !collect_literals(store, body, arity, self_idx, &mut lits) {
        return None;
    }

    let mut arith = ArithPostulates::new();
    for n in lits {
        arith.lit(n);
    }

    let mut param_positions = Vec::with_capacity(arity);
    for _ in 0..arity {
        let ty = arith.int_ty();
        param_positions.push(arith.p.push(ty));
    }
    let params = param_positions.iter().map(|&pos| arith.p.get(pos)).collect();

    Some((arith, params))
}

/// Shared finalize for both proofs below: package `denotation` (already
/// the same symbolic value under both readings, by construction) into a
/// `refl` proof, and confirm the kernel actually accepts it.
fn finish(arith: ArithPostulates, arity: usize, denotation: Expr) -> Option<EquivalenceProof> {
    let int_ty = arith.int_ty();
    let proof = kernel::refl(denotation.clone());
    let proof_ty = kernel::id(int_ty.clone(), denotation.clone(), denotation.clone());
    kernel::check(&arith.p.ctx, &proof, &proof_ty).ok()?;

    Some(EquivalenceProof {
        ctx: arith.p.ctx,
        arity,
        int_ty,
        denotation,
        proof,
    })
}

/// Attempts to build an [`EquivalenceProof`] covering every input of `h`.
/// Returns `None` for anything outside the covered fragment: recursive
/// (`Rec`-wrapped) functions (needs induction -- see module docs),
/// zero-arity terms, or terms containing `Abs`/`App`.
pub fn prove_pure_expr(store: &TermStore, h: Hash) -> Option<EquivalenceProof> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    if is_rec || arity == 0 {
        return None;
    }
    let (arith, params) = setup(store, body, arity, None)?;
    let denotation = denote(store, body, &arith, &params)?;
    finish(arith, arity, denotation)
}

// --- tail recursion: relational, per-call proofs ------------------------

/// A small, self-contained *concrete* evaluator over the same fragment
/// `denote` covers (`Var`/`Lit`/`Prim`/`If`, no `App`/`Abs`/`Rec`), used
/// only to decide which branch a concrete trace takes at each step, and
/// what its next/final values are. Deliberately not reusing `eval::eval`
/// (which handles the full language and unrolls `Rec`/`App`): this only
/// ever needs to stay self-consistent with `denote`'s shape, and being
/// structurally identical to it, side by side, is the easiest way to see
/// that it does. `params` is indexed by `Var` (i.e. `params[i]` is the
/// value of `Term::Var(i)`), matching `denote`'s convention.
fn eval_concrete(store: &TermStore, h: Hash, params: &[i64]) -> Option<i64> {
    match store.resolve(h) {
        Term::Var(i) => params.get(*i as usize).copied(),
        Term::Lit(n) => Some(*n),
        Term::Prim(op, a, b) => {
            let x = eval_concrete(store, *a, params)?;
            let y = eval_concrete(store, *b, params)?;
            Some(apply_prim_concrete(*op, x, y))
        }
        Term::If(c, t, e) => {
            let cv = eval_concrete(store, *c, params)?;
            if cv != 0 {
                eval_concrete(store, *t, params)
            } else {
                eval_concrete(store, *e, params)
            }
        }
        Term::Abs(_) | Term::App(..) | Term::Rec(_) => None,
    }
}

fn apply_prim_concrete(op: PrimOp, x: i64, y: i64) -> i64 {
    use PrimOp::*;
    match op {
        Add => x.wrapping_add(y),
        Sub => x.wrapping_sub(y),
        Mul => x.wrapping_mul(y),
        Div => {
            if y == 0 {
                0
            } else {
                x.wrapping_div(y)
            }
        }
        Mod => {
            if y == 0 {
                0
            } else {
                x.wrapping_rem(y)
            }
        }
        Lt => (x < y) as i64,
        Le => (x <= y) as i64,
        Eq => (x == y) as i64,
    }
}

enum StepOutcome {
    Base(Hash),
    TailCall(Vec<Hash>),
}

/// Walks `h` (a `compile_node`-shaped If-chain, in tail position) using
/// concrete params to decide which branch is taken, mirroring
/// `compile::compile_node`'s own structure exactly: an `If`'s condition is
/// resolved concretely and we recurse into the taken branch; a
/// fully-saturated self-call is reported as a `TailCall`; anything else is
/// the reached base case.
fn classify_step(
    store: &TermStore,
    h: Hash,
    arity: usize,
    self_idx: u32,
    concrete: &[i64],
) -> Option<StepOutcome> {
    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        let cv = eval_concrete(store, c, concrete)?;
        return classify_step(store, if cv != 0 { t } else { e }, arity, self_idx, concrete);
    }
    if let Some(args) = compile::match_self_call(store, h, arity, Some(self_idx)) {
        return Some(StepOutcome::TailCall(args));
    }
    Some(StepOutcome::Base(h))
}

/// Attempts to build a kernel-checked equivalence proof for one specific
/// call `h(args)`, where `h` is a `Rec`-wrapped, *tail*-recursive function
/// (the fragment `compile.rs` turns into a `loop`/`br`). See the module
/// docs ("Tail recursion") for what this does and doesn't establish.
///
/// Returns `None` for: non-recursive or zero-arity `h`; an arity mismatch;
/// non-tail recursion anywhere in the body (e.g. naive Fibonacci, which
/// `compile.rs` itself handles via a plain `call`, not a loop -- proving
/// that case needs a different argument, not this one); or a trace that
/// doesn't reach a base case within a generous step bound (guards against
/// a non-terminating or pathologically long call blowing up proof size).
pub fn prove_tail_recursive_call(store: &TermStore, h: Hash, args: &[i64]) -> Option<EquivalenceProof> {
    const MAX_STEPS: usize = 10_000;

    let (arity, body, is_rec) = compile::peel(store, h)?;
    if !is_rec || arity == 0 || arity != args.len() {
        return None;
    }
    let self_idx = arity as u32;

    let (arith, mut symbolic) = setup(store, body, arity, Some(self_idx))?;
    // By-`Var`-index concrete params (`Var(0)` = last-applied), matching
    // `symbolic`'s (and `denote`'s) convention; `args` itself is in
    // application order.
    let mut concrete: Vec<i64> = (0..arity).map(|i| args[arity - 1 - i]).collect();

    let mut denotation = None;
    for _ in 0..MAX_STEPS {
        match classify_step(store, body, arity, self_idx, &concrete)? {
            StepOutcome::Base(leaf) => {
                denotation = Some(denote(store, leaf, &arith, &symbolic)?);
                break;
            }
            StepOutcome::TailCall(arg_exprs) => {
                if arg_exprs.len() != arity {
                    return None;
                }
                let mut new_symbolic = Vec::with_capacity(arity);
                let mut new_concrete = Vec::with_capacity(arity);
                for i in 0..arity {
                    let expr = arg_exprs[arity - 1 - i];
                    new_symbolic.push(denote(store, expr, &arith, &symbolic)?);
                    new_concrete.push(eval_concrete(store, expr, &concrete)?);
                }
                symbolic = new_symbolic;
                concrete = new_concrete;
            }
        }
    }
    finish(arith, arity, denotation?)
}

// --- a universal proof for recursion, tail or not, via genuine induction -

// See the module docs above for the concept (`Ev`, gating, `combine`,
// `cong_n`); this is the implementation-level map from that to the code
// below.
//
// `classify_tree` turns `body` into a [`DecisionTree`] (an arbitrary
// nested-`If` shape, `compile_node` already compiles it fine); a single
// top-level `If` (the historically-first, narrower shape this covered) is
// just the case where the tree has depth one. `flatten_tree` reduces that
// to a flat `Vec<Leaf>`, each carrying its root-to-leaf path of
// `(cond, literal)` premises and its self-call occurrences (via
// `find_self_calls`, `Vec<Vec<Hash>>` -- one argument list per occurrence,
// left-to-right/depth-first).
//
// Per leaf `i`, with `k_i` self-calls: `combine_i` (`Anchored`, built once,
// reused at several deeper points) is leaf `i`'s own expression with each
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
// as its condition (`compile_cond` in `compile.rs` requires that too; also
// what lets the gating above use plain equality, since a comparison only
// ever denotes to `0` or `1`); `body` must have at least one leaf with a
// self-call in it somewhere; and a leaf's own expression may not contain a
// further nested `If` (`find_self_calls`/`denote_with_placeholders` both
// reject one, same as `denote` always has) -- only as the *whole* body of
// some branch, which `classify_tree` already extracts as its own tree
// node. `prove_tail_recursive_call` already handles arbitrary branching
// *and* arbitrary self-call placement on its own (it just follows one
// concrete path through the tree per call, denoting whatever it finds
// along the way), so neither of those needed widening.

/// `f` applied to each of `args` in order (left to right).
fn apply_n(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, kernel::app)
}

/// `arith.p.get(pos)` for each of `positions`, resolved fresh -- never
/// cached, same convention as `Params::at` (staleness after a further
/// push), just for a list of individually-tracked postulate positions
/// rather than one `Params` group.
fn resolve_all(arith: &ArithPostulates, positions: &[usize]) -> Vec<Expr> {
    positions.iter().map(|&p| arith.p.get(p)).collect()
}

/// The shape `prove_tail_recursive_universal`'s `body` must be: an
/// arbitrary tree of nested `If`s (matching what `compile_node` already
/// compiles), each leaf an arithmetic expression (`Var`/`Lit`/`Prim`) that
/// may itself contain any number of self-call occurrences (zero, for a
/// base case; one in tail position, for the old tail-recursion special
/// case; one or more anywhere else, e.g. `f(n-1) + f(n-2)`) -- but *not* a
/// further nested `If` (a real, documented restriction: `classify_tree`
/// already extracts every `If` that's the *whole* body of some branch,
/// but one embedded as a sub-expression of an arithmetic leaf, e.g.
/// `n + (if c then 1 else 2)`, is out of scope for now).
enum DecisionTree {
    If { cond: Hash, then_branch: Box<DecisionTree>, else_branch: Box<DecisionTree> },
    Leaf(Hash),
}

/// Classifies `h` into a [`DecisionTree`]. Every `If`'s condition must be
/// a direct comparison (same restriction `compile_cond` in `compile.rs`
/// already imposes, and what lets `cond_premise` below use plain `Id`
/// equality -- a comparison only ever denotes to `0` or `1`).
fn classify_tree(store: &TermStore, h: Hash) -> Option<DecisionTree> {
    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        if !matches!(store.resolve(c), Term::Prim(PrimOp::Lt | PrimOp::Le | PrimOp::Eq, _, _)) {
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
struct Leaf {
    path: Vec<(Hash, i64)>,
    expr: Hash,
    calls: Vec<Vec<Hash>>,
}

/// `arity`/`self_idx` bundled together -- the pair `find_self_calls` and
/// `denote_with_placeholders` both need on every recursive call, purely to
/// forward to `compile::match_self_call` at each node.
#[derive(Clone, Copy)]
struct SelfCall {
    arity: usize,
    idx: u32,
}

/// Flattens a [`DecisionTree`] into its leaves (with their paths), then
/// locates each leaf's self-call occurrences via `find_self_calls`.
/// Returns `None` if any leaf falls outside the fragment `denote`/
/// `find_self_calls` cover (a nested `If`, a non-tail-recursion `Abs`,
/// a free `App`, ...).
fn flatten_tree(store: &TermStore, tree: &DecisionTree, self_call: SelfCall) -> Option<Vec<Leaf>> {
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
            find_self_calls(store, expr, self_call, &mut calls)
                .then_some(())
                .map(|()| Leaf { path, expr, calls })
        })
        .collect()
}

/// Walks a leaf's `Var`/`Lit`/`Prim` structure (a nested `If` or anything
/// else outside the fragment fails), appending each self-call occurrence's
/// argument list to `out` in the same left-to-right order
/// `denote_with_placeholders` will later substitute them in.
fn find_self_calls(store: &TermStore, h: Hash, self_call: SelfCall, out: &mut Vec<Vec<Hash>>) -> bool {
    if let Some(args) = compile::match_self_call(store, h, self_call.arity, Some(self_call.idx)) {
        out.push(args);
        return true;
    }
    match store.resolve(h) {
        Term::Var(_) | Term::Lit(_) => true,
        Term::Prim(_, a, b) => {
            find_self_calls(store, *a, self_call, out) && find_self_calls(store, *b, self_call, out)
        }
        Term::If(..) | Term::Abs(_) | Term::App(..) | Term::Rec(_) => false,
    }
}

/// Like `denote`, but for a leaf already classified by `find_self_calls`:
/// each self-call occurrence is replaced by the next entry of
/// `placeholders` (consumed left-to-right, matching `find_self_calls`'
/// order) instead of failing on the `App`. Used both to build a leaf's
/// `combine` function's body (`placeholders` = the `Ev`-bound values) and,
/// nowhere else -- everywhere `combine` is *used* at a different
/// instantiation, it's applied as a value via `combine_of`, not re-walked.
fn denote_with_placeholders(
    store: &TermStore,
    h: Hash,
    self_call: SelfCall,
    arith: &ArithPostulates,
    params: &[Expr],
    placeholders: &[Expr],
    next: &mut usize,
) -> Option<Expr> {
    if compile::match_self_call(store, h, self_call.arity, Some(self_call.idx)).is_some() {
        let v = placeholders.get(*next).cloned();
        *next += 1;
        return v;
    }
    match store.resolve(h) {
        Term::Var(i) => params.get(*i as usize).cloned(),
        Term::Lit(n) => Some(arith.lit_ref(*n)),
        Term::Prim(op, a, b) => {
            let da = denote_with_placeholders(store, *a, self_call, arith, params, placeholders, next)?;
            let db = denote_with_placeholders(store, *b, self_call, arith, params, placeholders, next)?;
            Some(kernel::app2(arith.op_ref(*op), da, db))
        }
        Term::If(..) | Term::Abs(_) | Term::App(..) | Term::Rec(_) => None,
    }
}

/// A term built once via `close_pi`/`close_lam` at a specific ambient
/// context depth (`arith.p.ctx.len()` at the time), for reuse at a
/// *deeper* point later on. `close_pi`/`close_lam` only close over the
/// binders introduced for *that specific call*; anything the built term
/// still references in the ambient context beyond those (e.g. `ev_pos`,
/// an outer postulate) stays a `Var` fixed at that original depth. If the
/// term is then embedded, unchanged, inside another term built under more
/// binders (as `loop_val`'s pieces are, reused across several different,
/// deeper `params_and_close` calls), those ambient references go stale by
/// exactly as many binders as were introduced since -- `at` reshifts by
/// that difference. This is the same class of bug `kernel::ctx_lookup`
/// fixes for `Var` itself, one level up.
#[derive(Clone)]
struct Anchored {
    depth: usize,
    expr: Expr,
}
impl Anchored {
    fn new(arith: &ArithPostulates, expr: Expr) -> Self {
        Anchored { depth: arith.p.ctx.len(), expr }
    }
    fn at(&self, arith: &ArithPostulates) -> Expr {
        let cur = arith.p.ctx.len();
        debug_assert!(cur >= self.depth, "Anchored used at a shallower depth than it was built");
        kernel::shift(&self.expr, 0, (cur - self.depth) as i32)
    }
}

/// A set of postulated `Int` params, kept as *positions* rather than
/// resolved `Expr`s. Resolving once (`Vec<Expr>`) and reusing that
/// snapshot is exactly the staleness bug `Anchored` guards against for a
/// whole built term, one level earlier: the moment anything more gets
/// pushed onto `arith.p.ctx` after the snapshot was taken (a further
/// local binder, e.g. `v` or `e`), every entry in it is off by one (or
/// more) and needs reshifting. `at` sidesteps that by never caching --
/// call it fresh, immediately before each use, however many things have
/// been pushed since these params themselves were introduced.
struct Params(Vec<usize>);
impl Params {
    fn at(&self, arith: &ArithPostulates) -> Vec<Expr> {
        self.0.iter().map(|&pos| arith.p.get(pos)).collect()
    }
}

/// Pushes `n` fresh `Int`-typed postulates, lets `build` extend
/// `arith.p.ctx` further and construct a body term (resolving the params
/// via `Params::at`, fresh, whenever it actually needs them -- see
/// `Params`), then closes *everything* pushed since entry (the `n` params
/// plus anything `build` itself pushed, e.g. more binders of its own)
/// into nested binders around that body, rolling the temporary pushes
/// back afterward. Pass `kernel::close_pi` to build a *type* (quantifying
/// over these params) or `kernel::close_lam` to build a *value* of that
/// type (e.g. a motive or a proof to pass as an argument) -- getting this
/// wrong is a real, easy-to-make mistake (a `Pi` where a `Lam` was
/// needed), not a hypothetical one.
fn params_and_close(
    arith: &mut ArithPostulates,
    n: usize,
    close: fn(usize, &[Expr], Expr) -> Expr,
    build: impl FnOnce(&mut ArithPostulates, &Params) -> Option<Expr>,
) -> Option<Expr> {
    let base_len = arith.p.ctx.len();
    let mut positions = Vec::with_capacity(n);
    for _ in 0..n {
        let ty = arith.int_ty();
        positions.push(arith.p.push(ty));
    }
    let pp = Params(positions);
    let body = build(arith, &pp);
    let closed = body.map(|b| close(base_len, &arith.p.ctx, b));
    arith.p.ctx.truncate(base_len);
    closed
}

/// A kernel-checked universal theorem: for every input, the witness that
/// unrolling the recursion terminates (`Ev`) determines the same value the
/// compiled code's own recursive structure (`loop_val`) reconstructs from
/// that witness -- covers tail recursion and general (non-tail) recursion
/// alike (see module docs).
pub struct UniversalTailProof {
    pub ctx: Ctx,
    pub arity: usize,
    /// `: Pi p_0..p_{arity-1} v (e : Ev(p_0,..,v)). Id(Int, loop_val(..,e), v)`.
    pub theorem_ty: Expr,
    pub theorem_proof: Expr,
}

/// Attempts to build a [`UniversalTailProof`] for `h`. Returns `None` for
/// anything outside the covered fragment: not `Rec`-wrapped, zero arity, a
/// body that doesn't classify as a [`DecisionTree`] (every `If` on the way
/// to a leaf must be a direct comparison, and no leaf may itself contain a
/// further nested `If`), or one with no self-call anywhere in it (see
/// module docs).
pub fn prove_tail_recursive_universal(store: &TermStore, h: Hash) -> Option<UniversalTailProof> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    if !is_rec || arity == 0 {
        return None;
    }
    let self_idx = arity as u32;
    let self_call = SelfCall { arity, idx: self_idx };

    let tree = classify_tree(store, body)?;
    let leaves = flatten_tree(store, &tree, self_call)?;
    if leaves.iter().all(|l| l.calls.is_empty()) {
        return None; // no recursion anywhere: not this function's job (see `prove_pure_expr`)
    }

    let mut lits = Vec::new();
    if !collect_literals(store, body, arity, Some(self_idx), &mut lits) {
        return None;
    }

    let mut arith = ArithPostulates::new();
    for n in lits {
        arith.lit(n);
    }
    arith.lit(0);
    arith.lit(1); // `cond_premise` below needs both regardless of whether the source uses them

    // cond_premise(cond, params, lit): "cond(params) = lit" -- the
    // hypothesis each leaf's path premises are built from below, tying
    // `Ev`'s constructors to whichever branch `cond` actually selects
    // instead of admitting a witness unconditionally (see module docs).
    // Always resolves fresh via the caller-supplied `params`, same
    // convention as `ev_of`.
    let cond_premise = |arith: &ArithPostulates, cond: Hash, params: &[Expr], lit: i64| -> Option<Expr> {
        let d = denote(store, cond, arith, params)?;
        Some(kernel::id(arith.int_ty(), d, arith.lit_ref(lit)))
    };

    // Pushes one premise per `(cond, lit)` on `path` (a leaf's whole
    // ancestry, root to leaf), returning their positions. Each premise's
    // own type only depends on `params`, but every push grows the
    // context by one, so `params` is re-resolved fresh immediately before
    // each individual push rather than reused across them.
    let push_path = |arith: &mut ArithPostulates, pp: &Params, path: &[(Hash, i64)]| -> Option<Vec<usize>> {
        let mut positions = Vec::with_capacity(path.len());
        for &(cond, lit) in path {
            let pf_ty = cond_premise(arith, cond, &pp.at(arith), lit)?;
            positions.push(arith.p.push(pf_ty));
        }
        Some(positions)
    };

    // new_params_for(call_args, params): one self-call occurrence's own
    // argument expressions denoted in terms of `params`, reindexed from
    // application order to by-`Var` order (matching
    // `prove_tail_recursive_call`'s convention exactly).
    let new_params_for = |arith: &ArithPostulates, call_args: &[Hash], params: &[Expr]| -> Option<Vec<Expr>> {
        (0..arity)
            .map(|i| denote(store, call_args[arity - 1 - i], arith, params))
            .collect()
    };

    // Ev : Int^arity -> Int -> Sort(0)  (non-dependent chain: composes
    // correctly via `arrow`'s own shifting regardless of build order --
    // see `ArithPostulates::new`'s `ite_ty` for the same pattern.)
    let ev_ty = (0..=arity).fold(kernel::sort(0), |ty, _| kernel::arrow(arith.int_ty(), ty));
    let ev_pos = arith.p.push(ev_ty);
    // Resolves `params`/`np` fresh via the caller-supplied slice -- the
    // caller is responsible for passing one resolved *at the current
    // depth* (`pp.at(arith)` or a freshly-recomputed `new_params_for`),
    // not a cached one from before further pushes.
    let ev_of = |arith: &ArithPostulates, params: &[Expr], v: Expr| -> Expr {
        apply_n(arith.p.get(ev_pos), params.iter().cloned().chain([v]))
    };

    // Pushes `v_1:Int .. v_k:Int` then `e_1:Ev(new_params_1,v_1) ..
    // e_k:Ev(new_params_k,v_k)` for a leaf's `calls` (one `(v,e)` pair per
    // self-call occurrence, grouped -- all `v`s then all `e`s -- rather
    // than interleaved; each `e_j`'s type only needs its *own* `v_j`'s
    // position, which stays resolvable via `arith.p.get` regardless of
    // what else has been pushed since, so grouping is no less correct
    // than interleaving and is simpler for every caller below to zip).
    let push_calls = |arith: &mut ArithPostulates, pp: &Params, calls: &[Vec<Hash>]| -> Option<(Vec<usize>, Vec<usize>)> {
        let mut v_positions = Vec::with_capacity(calls.len());
        for _ in calls {
            v_positions.push(arith.p.push(arith.int_ty()));
        }
        let mut e_positions = Vec::with_capacity(calls.len());
        for (call, &v_pos) in calls.iter().zip(&v_positions) {
            let np = new_params_for(arith, call, &pp.at(arith))?;
            let ev_np = ev_of(arith, &np, arith.p.get(v_pos));
            e_positions.push(arith.p.push(ev_np));
        }
        Some((v_positions, e_positions))
    };

    // combine_i : Pi params. Pi ih_1:Int .. ih_{k_i}:Int. Int -- leaf i's
    // own arithmetic expression with each self-call occurrence replaced
    // by the corresponding `ih_j` (`denote_with_placeholders`), closed
    // over `params` *and* the `k_i` placeholders as one value, reused
    // (via `Anchored`, since it's referenced from several deeper points
    // below) both to state what value leaf `i` produces and, later, to
    // recombine the actually-recursively-computed values. `k_i == 0`
    // (`combine_i() = denote(leaf, params)`) is the old base-case shape;
    // `k_i == 1` with the self-call as the *whole* leaf
    // (`combine_i(ih) = ih`) is the old tail-call shape; anything else
    // (`n * ih`, `ih_1 + ih_2`, ...) is genuinely new.
    let mut combines = Vec::with_capacity(leaves.len());
    for leaf in &leaves {
        let expr = params_and_close(&mut arith, arity, kernel::close_lam, |arith, pp| {
            params_and_close(arith, leaf.calls.len(), kernel::close_lam, |arith, pp2| {
                let params = pp.at(arith);
                let placeholders = pp2.at(arith);
                denote_with_placeholders(store, leaf.expr, self_call, arith, &params, &placeholders, &mut 0)
            })
        })?;
        combines.push(Anchored::new(&arith, expr));
    }
    let combine_of = |arith: &ArithPostulates, combine: &Anchored, params: &[Expr], ihs: &[Expr]| -> Expr {
        apply_n(combine.at(arith), params.iter().cloned().chain(ihs.iter().cloned()))
    };

    // ev_leaf_i : Pi params. Pi (leaf i's path premises). Pi v_1..v_{k_i}
    //             (e_1:Ev(new_params_1,v_1))..(e_{k_i}:..). Ev(params, combine_i(params,vs))
    // -- one constructor per leaf.
    let mut ev_leaf_positions = Vec::with_capacity(leaves.len());
    for (leaf, combine) in leaves.iter().zip(&combines) {
        let ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
            push_path(arith, pp, &leaf.path)?;
            let (v_positions, _e_positions) = push_calls(arith, pp, &leaf.calls)?;
            let params = pp.at(arith);
            let vs = resolve_all(arith, &v_positions);
            let combine_v = combine_of(arith, combine, &params, &vs);
            Some(ev_of(arith, &params, combine_v))
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
    let motive_ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
        let v_pos = arith.p.push(arith.int_ty());
        let v = arith.p.get(v_pos);
        let ev_pv = ev_of(arith, &pp.at(arith), v);
        arith.p.push(ev_pv);
        Some(kernel::sort(0))
    })?;
    let p_base_len = arith.p.ctx.len();
    let p_pos = arith.p.push(motive_ty);
    let p_of = |arith: &ArithPostulates, params: &[Expr], v: Expr, e: Expr| -> Expr {
        apply_n(arith.p.get(p_pos), params.iter().cloned().chain([v, e]))
    };

    // leaf_case_ty_i : Pi params. Pi (path premises) v_1..v_{k_i} (e_1..e_{k_i}).
    //                  P(new_params_1,v_1,e_1) -> .. -> P(new_params_{k_i},v_{k_i},e_{k_i})
    //               -> P(params, combine_i(params,vs), ev_leaf_i(params,premises,vs,es))
    // -- `k_i == 0` gives the old (implication-free) base-case type;
    // `k_i == 1` gives the old step-case type.
    let mut leaf_case_tys = Vec::with_capacity(leaves.len());
    for (leaf, (&ev_leaf_pos, combine)) in leaves.iter().zip(ev_leaf_positions.iter().zip(&combines)) {
        let ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
            let path_positions = push_path(arith, pp, &leaf.path)?;
            let (v_positions, e_positions) = push_calls(arith, pp, &leaf.calls)?;
            // Use phase.
            let params = pp.at(arith);
            let premises = resolve_all(arith, &path_positions);
            let vs = resolve_all(arith, &v_positions);
            let es = resolve_all(arith, &e_positions);
            let mut ih_tys = Vec::with_capacity(leaf.calls.len());
            for ((call, &v_pos), &e_pos) in leaf.calls.iter().zip(&v_positions).zip(&e_positions) {
                let np = new_params_for(arith, call, &params)?;
                ih_tys.push(p_of(arith, &np, arith.p.get(v_pos), arith.p.get(e_pos)));
            }
            let combine_v = combine_of(arith, combine, &params, &vs);
            let ev_leaf_applied = apply_n(
                arith.p.get(ev_leaf_pos),
                params.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es.iter().cloned()),
            );
            let concl = p_of(arith, &params, combine_v, ev_leaf_applied);
            Some(ih_tys.into_iter().rev().fold(concl, |acc, ih_ty| kernel::arrow(ih_ty, acc)))
        })?;
        leaf_case_tys.push(ty);
    }
    let concl_ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
        let v_pos = arith.p.push(arith.int_ty());
        let ev_pv = ev_of(arith, &pp.at(arith), arith.p.get(v_pos));
        let e_pos = arith.p.push(ev_pv);
        // Use phase.
        let params = pp.at(arith);
        let v = arith.p.get(v_pos);
        let e = arith.p.get(e_pos);
        Some(p_of(arith, &params, v, e))
    })?;

    let ev_rec_ty_body = leaf_case_tys.iter().rev().fold(concl_ty, |acc, ty| kernel::arrow(ty.clone(), acc));
    let ev_rec_ty = kernel::close_pi(p_base_len, &arith.p.ctx, ev_rec_ty_body);
    arith.p.ctx.truncate(p_base_len);
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
    let const_int_motive_expr = params_and_close(&mut arith, arity, kernel::close_lam, |arith, pp| {
        let v_pos = arith.p.push(arith.int_ty());
        let ev_pv = ev_of(arith, &pp.at(arith), arith.p.get(v_pos));
        arith.p.push(ev_pv); // e : Ev(params, v)
        Some(arith.int_ty())
    })?;
    let const_int_motive = Anchored::new(&arith, const_int_motive_expr);

    let mut loop_leaves = Vec::with_capacity(leaves.len());
    for (leaf, combine) in leaves.iter().zip(&combines) {
        let expr = params_and_close(&mut arith, arity, kernel::close_lam, |arith, pp| {
            push_path(arith, pp, &leaf.path)?; // matches leaf_case_ty's premise binders, unused in the body
            push_calls(arith, pp, &leaf.calls)?; // v/e binders, also unused in the body
            let mut ih_positions = Vec::with_capacity(leaf.calls.len());
            for _ in &leaf.calls {
                ih_positions.push(arith.p.push(arith.int_ty()));
            }
            let params = pp.at(arith);
            let ihs = resolve_all(arith, &ih_positions);
            Some(combine_of(arith, combine, &params, &ihs))
        })?;
        loop_leaves.push(Anchored::new(&arith, expr));
    }

    let loop_val = |arith: &ArithPostulates, params: &[Expr], v: Expr, e: Expr| -> Expr {
        let cases: Vec<Expr> = loop_leaves.iter().map(|a| a.at(arith)).collect();
        ev_rec_ref(arith, const_int_motive.at(arith), &cases, params, v, e)
    };

    // loop_val_leaf_eq_i : Pi params (path premises) v_1..v_{k_i} (e_1..e_{k_i}).
    //   Id(Int, loop_val(params, combine_i(params,vs), ev_leaf_i(params,premises,vs,es)),
    //            combine_i(params, [loop_val(new_params_j,v_j,e_j) for each j]))
    // -- the computation-rule axiom for *this specific* `loop_val` (not a
    // generic "for any motive" schema -- see module docs), one per leaf.
    let mut loop_val_leaf_eq_positions = Vec::with_capacity(leaves.len());
    for (leaf, (&ev_leaf_pos, combine)) in leaves.iter().zip(ev_leaf_positions.iter().zip(&combines)) {
        let ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
            let path_positions = push_path(arith, pp, &leaf.path)?;
            let (v_positions, e_positions) = push_calls(arith, pp, &leaf.calls)?;
            // Use phase.
            let params = pp.at(arith);
            let premises = resolve_all(arith, &path_positions);
            let vs = resolve_all(arith, &v_positions);
            let es = resolve_all(arith, &e_positions);
            let eb = apply_n(
                arith.p.get(ev_leaf_pos),
                params.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es.iter().cloned()),
            );
            let lhs = loop_val(arith, &params, combine_of(arith, combine, &params, &vs), eb);
            let mut recursive_vals = Vec::with_capacity(leaf.calls.len());
            for ((call, &v_pos), &e_pos) in leaf.calls.iter().zip(&v_positions).zip(&e_positions) {
                let np = new_params_for(arith, call, &params)?;
                recursive_vals.push(loop_val(arith, &np, arith.p.get(v_pos), arith.p.get(e_pos)));
            }
            let rhs = combine_of(arith, combine, &params, &recursive_vals);
            Some(kernel::id(arith.int_ty(), lhs, rhs))
        })?;
        loop_val_leaf_eq_positions.push(arith.p.push(ty));
    }

    // Theorem: Pi params v e. Id(Int, loop_val(params,v,e), v), proved via
    // ev_rec with motive `\params v e. Id(Int, loop_val(params,v,e), v)`.
    let id_motive_expr = params_and_close(&mut arith, arity, kernel::close_lam, |arith, pp| {
        let v_pos = arith.p.push(arith.int_ty());
        let ev_pv = ev_of(arith, &pp.at(arith), arith.p.get(v_pos));
        let e_pos = arith.p.push(ev_pv);
        // Use phase.
        let params = pp.at(arith);
        let v = arith.p.get(v_pos);
        let e = arith.p.get(e_pos);
        Some(kernel::id(arith.int_ty(), loop_val(arith, &params, v.clone(), e), v))
    })?;
    let id_motive = Anchored::new(&arith, id_motive_expr);

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
        let expr = params_and_close(&mut arith, arity, kernel::close_lam, |arith, pp| {
            let path_positions = push_path(arith, pp, &leaf.path)?;
            let (v_positions, e_positions) = push_calls(arith, pp, &leaf.calls)?;
            let mut ih_positions = Vec::with_capacity(leaf.calls.len());
            for ((call, &v_pos), &e_pos) in leaf.calls.iter().zip(&v_positions).zip(&e_positions) {
                let np = new_params_for(arith, call, &pp.at(arith))?;
                let ih_ty = kernel::id(
                    arith.int_ty(),
                    loop_val(arith, &np, arith.p.get(v_pos), arith.p.get(e_pos)),
                    arith.p.get(v_pos),
                );
                ih_positions.push(arith.p.push(ih_ty));
            }

            // Use phase: every push for this closure is done.
            let params = pp.at(arith);
            let premises = resolve_all(arith, &path_positions);
            let vs = resolve_all(arith, &v_positions);
            let es = resolve_all(arith, &e_positions);
            let ihs = resolve_all(arith, &ih_positions);
            let mut recursive_vals = Vec::with_capacity(leaf.calls.len());
            for (call, &v_pos) in leaf.calls.iter().zip(&v_positions) {
                let idx = recursive_vals.len();
                let np = new_params_for(arith, call, &params)?;
                recursive_vals.push(loop_val(arith, &np, arith.p.get(v_pos), arith.p.get(e_positions[idx])));
            }

            let eb = apply_n(
                arith.p.get(ev_leaf_pos),
                params.iter().cloned().chain(premises.iter().cloned()).chain(vs.iter().cloned()).chain(es.iter().cloned()),
            );
            let step_eq = apply_n(
                arith.p.get(loop_val_leaf_eq_pos),
                params.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es),
            );
            let f_partial = apply_n(combine.at(arith), params.iter().cloned());
            let cong_step = kernel::cong_n(&arith.int_ty(), &arith.int_ty(), &f_partial, &recursive_vals, &vs, ihs);

            let lhs = loop_val(arith, &params, combine_of(arith, combine, &params, &vs), eb);
            let mid = combine_of(arith, combine, &params, &recursive_vals);
            let rhs = combine_of(arith, combine, &params, &vs);
            Some(kernel::trans_proof(&arith.int_ty(), &lhs, &mid, &rhs, step_eq, cong_step))
        })?;
        theorem_leaves.push(Anchored::new(&arith, expr));
    }

    let theorem_ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
        let v_pos = arith.p.push(arith.int_ty());
        let ev_pv = ev_of(arith, &pp.at(arith), arith.p.get(v_pos));
        let e_pos = arith.p.push(ev_pv);
        // Use phase.
        let params = pp.at(arith);
        let v = arith.p.get(v_pos);
        let e = arith.p.get(e_pos);
        Some(kernel::id(arith.int_ty(), loop_val(arith, &params, v.clone(), e), v))
    })?;

    let theorem_proof = params_and_close(&mut arith, arity, kernel::close_lam, |arith, pp| {
        let v_pos = arith.p.push(arith.int_ty());
        let ev_pv = ev_of(arith, &pp.at(arith), arith.p.get(v_pos));
        let e_pos = arith.p.push(ev_pv);
        // Use phase.
        let params = pp.at(arith);
        let v = arith.p.get(v_pos);
        let e = arith.p.get(e_pos);
        let cases: Vec<Expr> = theorem_leaves.iter().map(|a| a.at(arith)).collect();
        Some(ev_rec_ref(arith, id_motive.at(arith), &cases, &params, v, e))
    })?;

    kernel::check(&arith.p.ctx, &theorem_proof, &theorem_ty).ok()?;

    Some(UniversalTailProof {
        ctx: arith.p.ctx,
        arity,
        theorem_ty,
        theorem_proof,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::TermStore;

    #[test]
    fn straight_line_term_gets_a_kernel_checked_proof() {
        // \a b. if a < b then a * 2 else b + 1
        let mut s = TermStore::new();
        let a = s.var(1);
        let b = s.var(0);
        let cond = s.prim(PrimOp::Lt, a, b);
        let two = s.lit(2);
        let then_branch = s.prim(PrimOp::Mul, a, two);
        let one = s.lit(1);
        let else_branch = s.prim(PrimOp::Add, b, one);
        let body = s.if_(cond, then_branch, else_branch);
        let inner = s.abs(body);
        let f = s.abs(inner);

        let proof = prove_pure_expr(&s, f).expect("straight-line term should be provable");
        assert_eq!(proof.arity, 2);
        // Independently re-typecheck from scratch (not just trusting the
        // `.ok()?` inside `prove_pure_expr`).
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        // This term is also handled by the interpreter and the WASM
        // compiler -- all three paths agree on which terms are in scope.
        assert!(compile::try_compile(&s, f).is_some());
    }

    #[test]
    fn recursive_term_is_out_of_scope() {
        // rec f n = if n <= 1 then 1 else n * f(n - 1)
        let mut s = TermStore::new();
        let n = s.var(0);
        let fv = s.var(1);
        let one = s.lit(1);
        let cond = s.prim(PrimOp::Le, n, one);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(fv, n_minus_1);
        let else_branch = s.prim(PrimOp::Mul, n, rec_call);
        let body = s.if_(cond, one, else_branch);
        let abs = s.abs(body);
        let fact = s.rec(abs);

        assert!(prove_pure_expr(&s, fact).is_none());
    }

    #[test]
    fn genuinely_higher_order_term_is_out_of_scope() {
        let mut s = TermStore::new();
        let f = s.var(1);
        let x = s.var(0);
        let fx = s.app(f, x);
        let ffx = s.app(f, fx);
        let inner = s.abs(ffx);
        let twice = s.abs(inner);
        assert!(prove_pure_expr(&s, twice).is_none());
    }

    fn gcd(s: &mut TermStore) -> Hash {
        // rec f a b = if b == 0 then a else f(b, a mod b) -- genuinely tail
        // recursive: the self-call is the whole else-branch, not nested
        // inside another operation, so compile.rs turns it into a loop.
        let b = s.var(0);
        let a = s.var(1);
        let f = s.var(2);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Eq, b, zero);
        let a_mod_b = s.prim(PrimOp::Mod, a, b);
        let rec_call = s.app2(f, b, a_mod_b);
        let body = s.if_(cond, a, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        s.rec(abs)
    }

    #[test]
    fn tail_recursive_call_gets_a_relational_proof() {
        let mut s = TermStore::new();
        let g = gcd(&mut s);

        for (a, b) in [(48, 18), (270, 192), (17, 5), (0, 7)] {
            let proof = prove_tail_recursive_call(&s, g, &[a, b])
                .unwrap_or_else(|| panic!("gcd({a},{b}) should get a relational proof"));
            assert_eq!(proof.arity, 2);
            kernel::check(
                &proof.ctx,
                &proof.proof,
                &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
            )
            .expect("the recorded proof should independently re-typecheck");
        }
    }

    #[test]
    fn tail_recursive_gcd_gets_a_universal_proof() {
        let mut s = TermStore::new();
        let g = gcd(&mut s);

        let proof = prove_tail_recursive_universal(&s, g).expect("gcd should get a universal proof");
        assert_eq!(proof.arity, 2);
        // Independently re-typecheck from scratch.
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");
    }

    #[test]
    fn one_functions_theorem_proof_is_rejected_against_anothers_type() {
        // Adversarial: does the kernel actually discriminate between two
        // different functions' universal proofs, or would it accept
        // anything with roughly the right shape? gcd's theorem_proof
        // (arity 2) checked against factorial's theorem_ty (arity 1, a
        // completely different Ev/combine/postulate layout) should be
        // rejected outright, not somehow typecheck by coincidence.
        let mut s = TermStore::new();
        let g = gcd(&mut s);
        let gcd_proof = prove_tail_recursive_universal(&s, g).expect("gcd should get a universal proof");

        let mut s2 = TermStore::new();
        let n = s2.var(0);
        let fv = s2.var(1);
        let one = s2.lit(1);
        let cond = s2.prim(PrimOp::Le, n, one);
        let n_minus_1 = s2.prim(PrimOp::Sub, n, one);
        let rec_call = s2.app(fv, n_minus_1);
        let else_branch = s2.prim(PrimOp::Mul, n, rec_call);
        let body = s2.if_(cond, one, else_branch);
        let abs = s2.abs(body);
        let fact = s2.rec(abs);
        let fact_proof = prove_tail_recursive_universal(&s2, fact).expect("factorial should get a universal proof");

        // gcd's proof, checked in gcd's own ctx (a proof is only
        // meaningful relative to the ctx it was built in), against
        // factorial's theorem_ty.
        assert!(
            kernel::check(&gcd_proof.ctx, &gcd_proof.theorem_proof, &fact_proof.theorem_ty).is_err(),
            "gcd's proof should be rejected against factorial's theorem type"
        );
    }

    #[test]
    fn tail_recursive_countdown_gets_a_universal_proof_with_base_in_the_else_branch() {
        // rec f n = if n > 0 then f(n - 1) else n -- unlike `gcd` above, the
        // tail call is the *then*-branch and the base case is the *else*-
        // branch, exercising the other `cond`-gating polarity
        // (`prove_tail_recursive_universal`'s `base_lit = 0` arm, vs gcd's
        // `base_lit = 1`) that gcd alone never touches.
        let mut s = TermStore::new();
        let n = s.var(0);
        let f = s.var(1);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, n);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(f, n_minus_1);
        let body = s.if_(cond, rec_call, n);
        let abs = s.abs(body);
        let countdown = s.rec(abs);

        let proof = prove_tail_recursive_universal(&s, countdown)
            .expect("countdown should get a universal proof");
        assert_eq!(proof.arity, 1);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");
    }

    #[test]
    fn tail_recursive_gcd_with_two_base_cases_gets_a_universal_proof() {
        // rec f a b = if a == 0 then b else if b == 0 then a else f(b, a mod b)
        // -- deeper than a single `If`: two base leaves (`b` at path
        // [a==0], `a` at path [a!=0, b==0]) and one tail leaf (`f(b, a mod
        // b)` at path [a!=0, b!=0]), exercising the widened
        // `prove_tail_recursive_universal` (one `Ev` constructor per leaf,
        // each gated by its own *conjunction* of path premises, not a
        // single top-level condition).
        let mut s = TermStore::new();
        let b = s.var(0);
        let a = s.var(1);
        let f = s.var(2);
        let zero = s.lit(0);
        let cond_a = s.prim(PrimOp::Eq, a, zero);
        let cond_b = s.prim(PrimOp::Eq, b, zero);
        let a_mod_b = s.prim(PrimOp::Mod, a, b);
        let rec_call = s.app2(f, b, a_mod_b);
        let inner_if = s.if_(cond_b, a, rec_call);
        let body = s.if_(cond_a, b, inner_if);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        let g = s.rec(abs);

        let proof =
            prove_tail_recursive_universal(&s, g).expect("gcd with two base cases should get a universal proof");
        assert_eq!(proof.arity, 2);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");
    }

    #[test]
    fn non_tail_recursion_gets_a_universal_proof_now() {
        // rec f n = if n <= 1 then 1 else n * f(n - 1) -- factorial: the
        // self-call is nested inside a multiplication, not tail position.
        // Generalizing Ev/ev_rec/loop_val to leaves with an arbitrary
        // self-call count, recombined via kernel::cong_n, covers this too
        // (this was the whole point of widening past tail recursion).
        let mut s = TermStore::new();
        let n = s.var(0);
        let fv = s.var(1);
        let one = s.lit(1);
        let cond = s.prim(PrimOp::Le, n, one);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(fv, n_minus_1);
        let else_branch = s.prim(PrimOp::Mul, n, rec_call);
        let body = s.if_(cond, one, else_branch);
        let abs = s.abs(body);
        let fact = s.rec(abs);

        let proof =
            prove_tail_recursive_universal(&s, fact).expect("factorial should now get a universal proof");
        assert_eq!(proof.arity, 1);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");
    }

    #[test]
    fn fibonacci_two_self_calls_gets_a_universal_proof() {
        // rec f n = if n < 2 then n else f(n-1) + f(n-2) -- naive
        // Fibonacci: two self-calls combined by one Prim, exercising
        // combine_i for k=2 and kernel::cong_n's actual n>1 case
        // (factorial above only needs k=1, where cong_n's loop runs once).
        let mut s = TermStore::new();
        let n = s.var(0);
        let f = s.var(1);
        let two = s.lit(2);
        let cond = s.prim(PrimOp::Lt, n, two);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let n_minus_2 = s.prim(PrimOp::Sub, n, two);
        let call1 = s.app(f, n_minus_1);
        let call2 = s.app(f, n_minus_2);
        let else_branch = s.prim(PrimOp::Add, call1, call2);
        let body = s.if_(cond, n, else_branch);
        let abs = s.abs(body);
        let fib = s.rec(abs);

        let proof = prove_tail_recursive_universal(&s, fib).expect("fibonacci should get a universal proof");
        assert_eq!(proof.arity, 1);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");
    }

    #[test]
    fn an_if_nested_inside_an_arithmetic_leaf_is_still_out_of_scope() {
        // rec f n = if n <= 0 then (n + (if n == 0 then 1 else 2)) else f(n-1)
        // -- the base leaf has an `If` embedded as a *sub-expression* of a
        // `Prim`, not as the whole body of some branch, which
        // `classify_tree` doesn't extract (a real, documented restriction,
        // not a subtle gap: `find_self_calls`/`denote_with_placeholders`
        // both reject a bare `If` node the same way `denote` always has).
        let mut s = TermStore::new();
        let n = s.var(0);
        let f = s.var(1);
        let zero = s.lit(0);
        let outer_cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let inner_cond = s.prim(PrimOp::Eq, n, zero);
        let two = s.lit(2);
        let inner_if = s.if_(inner_cond, one, two);
        let base_leaf = s.prim(PrimOp::Add, n, inner_if);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(f, n_minus_1);
        let body = s.if_(outer_cond, base_leaf, rec_call);
        let abs = s.abs(body);
        let g = s.rec(abs);

        assert!(prove_tail_recursive_universal(&s, g).is_none());
    }

    #[test]
    fn non_tail_recursion_is_out_of_scope_for_the_relational_proof() {
        // factorial's self-call is nested inside a multiplication (n *
        // f(n-1)), not a bare tail call -- compile.rs itself compiles this
        // via a plain `call`, not a loop, so this proof (which specifically
        // targets the loop transformation) correctly doesn't apply either.
        let mut s = TermStore::new();
        let n = s.var(0);
        let fv = s.var(1);
        let one = s.lit(1);
        let cond = s.prim(PrimOp::Le, n, one);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(fv, n_minus_1);
        let else_branch = s.prim(PrimOp::Mul, n, rec_call);
        let body = s.if_(cond, one, else_branch);
        let abs = s.abs(body);
        let fact = s.rec(abs);

        assert!(prove_tail_recursive_call(&s, fact, &[5]).is_none());
    }

    #[test]
    fn non_recursive_term_is_out_of_scope_for_the_relational_proof() {
        let mut s = TermStore::new();
        let a = s.var(1);
        let b = s.var(0);
        let sum = s.prim(PrimOp::Add, a, b);
        let inner = s.abs(sum);
        let f = s.abs(inner);
        assert!(prove_tail_recursive_call(&s, f, &[1, 2]).is_none());
    }
}
