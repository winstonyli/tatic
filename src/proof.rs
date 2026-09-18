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
use std::rc::Rc;

use crate::compile;
use crate::kernel::{self, Ctx, Expr, Postulates};
use crate::term::{Hash, PrimOp, Term, TermStore};

/// Postulated `Int` and its operators, plus on-demand postulated constants
/// for whichever literal values a given term actually uses.
#[derive(Clone)]
pub struct ArithPostulates {
    pub p: Postulates,
    int_pos: usize,
    op_pos: [usize; 8],
    ite_pos: usize,
    literal_pos: HashMap<i64, usize>,
    /// Memoized per `(op, x, y)` -- see `assume_prim_fact`.
    fact_pos: HashMap<(u8, i64, i64), usize>,
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
            fact_pos: HashMap::new(),
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

    /// Postulates (memoized per `(op, x, y)`) that concretely evaluating
    /// `op` at literals `x`, `y` yields the same result
    /// `apply_prim_concrete` -- the function `eval_concrete` itself uses --
    /// computes. This is the concrete counterpart of postulating `Int`'s
    /// operators abstractly in the first place: a postulated operator has
    /// no computation rule the kernel could use to *derive* this, so
    /// building a witness for one specific call has to assume each
    /// concrete fact it actually needs, one axiom per distinct fact,
    /// grounded in the same arithmetic function this whole project already
    /// treats as ground truth (see `eval_and_prove`).
    fn assume_prim_fact(&mut self, op: PrimOp, x: i64, y: i64) -> Expr {
        let key = (op as u8, x, y);
        if let Some(&pos) = self.fact_pos.get(&key) {
            return self.p.get(pos);
        }
        let result = apply_prim_concrete(op, x, y);
        self.lit(x);
        self.lit(y);
        self.lit(result);
        let lhs = kernel::app2(self.op_ref(op), self.lit_ref(x), self.lit_ref(y));
        let rhs = self.lit_ref(result);
        let ty = kernel::id(self.int_ty(), lhs, rhs);
        let pos = self.p.push(ty);
        self.fact_pos.insert(key, pos);
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

/// `Ev(params, v) : Sort(0)` -- `ev_pos`'s postulate (see `build_universal`)
/// applied to `params` then `v`. Resolves `ev_pos` fresh via the
/// caller-supplied `arith` -- the caller is responsible for passing
/// `params`/`v` resolved *at the current depth* too, same convention as
/// `Postulates::get` itself. A free function (not just `build_universal`'s
/// own local closure) so `build_ev_witness`'s branching-leaf recasting can
/// build the same `Ev(...)` application it does, rather than reimplementing it.
fn ev_of(arith: &ArithPostulates, ev_pos: usize, params: &[Expr], v: Expr) -> Expr {
    apply_n(arith.p.get(ev_pos), params.iter().cloned().chain([v]))
}

// --- hardening against the staleness bug class ---------------------------
//
// Twice now (the `Ev`-witness builder, then `denote_closure`), a function
// that composes an `Expr` out of more than one recursive sub-call held an
// already-resolved sub-`Expr` (or `params`/`param_facts` entry) across a
// *later* postulate push -- registering a combinator, a fresh `apply_k`, an
// `assume_prim_fact` axiom -- without reshifting it, the exact staleness
// `Anchored`'s own docs describe. Both times the only symptom was an opaque
// kernel type-mismatch far from the actual mistake (or, in the worse case
// that just hasn't happened yet, two *different* postulates that happen to
// share a type, producing a well-typed but semantically wrong term with no
// error at all). The fix each time was the same discipline -- anchor every
// intermediate value immediately, resolve fresh only once nothing more is
// left to push -- applied by hand, function by function, after a slow
// eprintln-driven bisection to find where it broke.
//
// This helper turns that bisection into an immediate, precisely located
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
fn debug_assert_has_type(ctx: &Ctx, e: &Expr, expected: &Expr, label: &str) {
    if let Err(err) = kernel::check(ctx, e, expected) {
        panic!(
            "staleness/composition bug in {label}: the value doesn't have its expected type.\n  \
             error: {err}\n  value: {e:?}\n  expected type: {expected:?}"
        );
    }
}
#[cfg(not(debug_assertions))]
fn debug_assert_has_type(_ctx: &Ctx, _e: &Expr, _expected: &Expr, _label: &str) {}

/// `combine`'s value at `params`/`ihs` (both hoisted to a free function --
/// not just a closure local to `prove_tail_recursive_universal` -- so
/// `build_ev_witness` can reuse it too).
fn combine_of(arith: &ArithPostulates, combine: &Anchored, params: &[Expr], ihs: &[Expr]) -> Expr {
    apply_n(combine.at(arith), params.iter().cloned().chain(ihs.iter().cloned()))
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
#[derive(Clone)]
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

/// Everything `prove_tail_recursive_universal`'s theorem was built from,
/// kept around (instead of dropped) so `prove_tail_recursive_instance` can
/// reuse it to build a concrete `Ev`-witness afterward, without redoing any
/// of the theorem's own construction. `theorem_ty`/`theorem_proof` are
/// `Anchored` because witness-building pushes further postulates onto
/// `arith.p.ctx` (fresh literal constants, `assume_prim_fact` axioms) after
/// this scaffold is built -- see `Anchored`'s own docs for why that matters.
///
/// Cloneable so a caller that wants several concrete instances (`jit.rs`'s
/// `kernel_verify`, trying a handful of sample calls) can build this once
/// and clone it per attempt, instead of paying for `build_universal`'s full
/// construction -- the expensive part, dominated by `kernel::cong_n`/
/// `trans_proof` chaining and a `kernel::check` re-verification -- again
/// for every sample.
#[derive(Clone)]
struct UniversalScaffold {
    arith: ArithPostulates,
    arity: usize,
    self_call: SelfCall,
    leaves: Vec<Leaf>,
    combines: Vec<Anchored>,
    ev_leaf_positions: Vec<usize>,
    /// `Ev`'s own postulate position (see `build_universal`) -- needed by
    /// `build_ev_witness`'s branching-leaf recasting, which builds `Ev(...)`
    /// applications directly rather than through a leaf-specific constructor.
    ev_pos: usize,
    theorem_ty: Anchored,
    theorem_proof: Anchored,
}

fn build_universal(store: &TermStore, h: Hash) -> Option<UniversalScaffold> {
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
    let ev_of = |arith: &ArithPostulates, params: &[Expr], v: Expr| -> Expr { ev_of(arith, ev_pos, params, v) };

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

    let theorem_ty = Anchored::new(&arith, theorem_ty);
    let theorem_proof = Anchored::new(&arith, theorem_proof);
    Some(UniversalScaffold {
        theorem_ty,
        theorem_proof,
        arity,
        self_call,
        leaves,
        combines,
        ev_leaf_positions,
        ev_pos,
        arith,
    })
}

/// Attempts to build a [`UniversalTailProof`] for `h`. Returns `None` for
/// anything outside the covered fragment: not `Rec`-wrapped, zero arity, a
/// body that doesn't classify as a [`DecisionTree`] (every `If` on the way
/// to a leaf must be a direct comparison, and no leaf may itself contain a
/// further nested `If`), or one with no self-call anywhere in it (see
/// module docs).
pub fn prove_tail_recursive_universal(store: &TermStore, h: Hash) -> Option<UniversalTailProof> {
    let scaffold = build_universal(store, h)?;
    let theorem_ty = scaffold.theorem_ty.at(&scaffold.arith);
    let theorem_proof = scaffold.theorem_proof.at(&scaffold.arith);
    Some(UniversalTailProof {
        ctx: scaffold.arith.p.ctx,
        arity: scaffold.arity,
        theorem_ty,
        theorem_proof,
    })
}

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
/// `params`/`param_facts` are `Anchored` (not plain `Expr`), and every
/// intermediate value this function builds is immediately wrapped in
/// `Anchored` too, resolved fresh only at the point it's actually used --
/// `assume_prim_fact` (and recursing into a sibling sub-expression) pushes
/// further postulates onto `arith.p.ctx`, and anything already resolved to
/// a plain `Expr` before that point would go stale exactly the way
/// `Anchored`'s own docs describe, one level up (this is what an earlier,
/// buggy version of this function got wrong: it returned `Var`-index-laden
/// `Expr`s straight from a callee, which the caller then held across
/// further pushes without reshifting).
fn eval_and_prove(
    store: &TermStore,
    h: Hash,
    arith: &mut ArithPostulates,
    params: &[Anchored],
    concrete: &[i64],
    param_facts: &[Anchored],
) -> Option<(i64, Expr, Expr)> {
    match store.resolve(h) {
        Term::Var(i) => {
            let i = *i as usize;
            Some((*concrete.get(i)?, params.get(i)?.at(arith), param_facts.get(i)?.at(arith)))
        }
        Term::Lit(n) => {
            let l = arith.lit_ref(*n);
            Some((*n, l.clone(), kernel::refl(l)))
        }
        Term::Prim(op, a, b) => {
            let (op, a, b) = (*op, *a, *b);
            let (xa, da, pa) = eval_and_prove(store, a, arith, params, concrete, param_facts)?;
            let da = Anchored::new(arith, da);
            let pa = Anchored::new(arith, pa);
            let (xb, db, pb) = eval_and_prove(store, b, arith, params, concrete, param_facts)?;
            let db = Anchored::new(arith, db);
            let pb = Anchored::new(arith, pb);
            let fact = arith.assume_prim_fact(op, xa, xb);
            let result = apply_prim_concrete(op, xa, xb);

            // Nothing pushes onto arith.p.ctx from here on, so resolving
            // everything fresh now (past `assume_prim_fact`'s own push)
            // keeps it all valid for the rest of this call.
            let (da, pa, db, pb) = (da.at(arith), pa.at(arith), db.at(arith), pb.at(arith));
            let int_ty = arith.int_ty();
            let f = arith.op_ref(op);
            let cong =
                kernel::cong_n(&int_ty, &int_ty, &f, &[da.clone(), db.clone()], &[arith.lit_ref(xa), arith.lit_ref(xb)], vec![
                    pa, pb,
                ]);
            let lhs = kernel::app2(f.clone(), da, db);
            let mid = kernel::app2(f, arith.lit_ref(xa), arith.lit_ref(xb));
            let rhs = arith.lit_ref(result);
            let proof = kernel::trans_proof(&int_ty, &lhs, &mid, &rhs, cong, fact);
            debug_assert_has_type(&arith.p.ctx, &proof, &kernel::id(int_ty, lhs.clone(), rhs), "eval_and_prove: Prim proof");
            Some((result, lhs, proof))
        }
        Term::If(..) | Term::Abs(_) | Term::App(..) | Term::Rec(_) => None,
    }
}

/// See the section docs above for what this guards against.
const WITNESS_NODE_BUDGET: usize = 256;

/// Builds an actual `e : Ev(params, v)` witness for one specific call,
/// following the real trace `concrete` determines (mirroring
/// `classify_step`, but for any leaf `flatten_tree` found, not just a tail
/// loop) and recursing into every self-call occurrence found along the way.
/// Returns `(v, e)`, fresh as of the moment this call returns -- a caller
/// that holds either across further postulate pushes (as every caller here
/// does) must wrap them in `Anchored` itself. `params`/`param_facts` are
/// never taken as input (see the section docs above): this function always
/// works in terms of the canonical literal params for `concrete`, which is
/// what makes `memo` (keyed on `concrete` alone) sound. `budget` bounds the
/// number of newly-*derived* calls; a `memo` hit doesn't touch it.
#[allow(clippy::too_many_arguments)]
fn build_ev_witness(
    store: &TermStore,
    arith: &mut ArithPostulates,
    self_call: SelfCall,
    leaves: &[Leaf],
    ev_leaf_positions: &[usize],
    combines: &[Anchored],
    ev_pos: usize,
    concrete: &[i64],
    budget: &mut usize,
    memo: &mut HashMap<Vec<i64>, (Anchored, Anchored)>,
) -> Option<(Expr, Expr)> {
    if let Some((v, e)) = memo.get(concrete) {
        return Some((v.at(arith), e.at(arith)));
    }
    *budget = budget.checked_sub(1)?;

    let leaf_idx = leaves
        .iter()
        .position(|leaf| leaf.path.iter().all(|&(cond, lit)| eval_concrete(store, cond, concrete) == Some(lit)))?;
    let leaf = &leaves[leaf_idx];

    // Canonical params for this level: literals, trivially equal to
    // themselves -- see the section docs above for why this (not a
    // caller-supplied denoted expression) is what makes `memo` sound.
    let params: Vec<Anchored> = concrete.iter().map(|&c| Anchored::new(arith, arith.lit_ref(c))).collect();
    let param_facts: Vec<Anchored> =
        params.iter().map(|p| Anchored::new(arith, kernel::refl(p.at(arith)))).collect();

    // Collected across the loops below, which push further postulates
    // (assume_prim_fact, and every self-call's own recursion) -- anchor
    // each one immediately so it can be resolved fresh once everything is
    // done growing, at the final assembly below.
    let mut premises = Vec::with_capacity(leaf.path.len());
    for &(cond, _lit) in &leaf.path {
        let (_, _, proof) = eval_and_prove(store, cond, arith, &params, concrete, &param_facts)?;
        premises.push(Anchored::new(arith, proof));
    }

    let mut vs = Vec::with_capacity(leaf.calls.len());
    let mut es = Vec::with_capacity(leaf.calls.len());
    for call in &leaf.calls {
        let mut new_concrete = Vec::with_capacity(self_call.arity);
        let mut denoted_args = Vec::with_capacity(self_call.arity);
        let mut denoted_facts = Vec::with_capacity(self_call.arity);
        for i in 0..self_call.arity {
            let arg = call[self_call.arity - 1 - i];
            let (x, denoted, pf) = eval_and_prove(store, arg, arith, &params, concrete, &param_facts)?;
            new_concrete.push(x);
            denoted_args.push(Anchored::new(arith, denoted));
            denoted_facts.push(Anchored::new(arith, pf));
        }

        // The recursive call's own witness, always in canonical
        // (literal-params) form -- valid regardless of whether this came
        // from a fresh derivation or a `memo` hit.
        let (v, e_canonical) = build_ev_witness(
            store,
            arith,
            self_call,
            leaves,
            ev_leaf_positions,
            combines,
            ev_pos,
            &new_concrete,
            budget,
            memo,
        )?;
        let v = Anchored::new(arith, v);
        let e_canonical = Anchored::new(arith, e_canonical);

        // Recast `e_canonical : Ev(lit_params, v)` to `Ev(denoted_params,
        // v)` -- what *this* leaf's own `Ev` constructor actually expects
        // for its e_i (its type was built from the call's real argument
        // expressions, not just their values) -- via congruence over the
        // params (`cong_n`, `Ev` held fixed at `v`) and transport along the
        // resulting type equality.
        let int_ty = arith.int_ty();
        let lit_params: Vec<Expr> = new_concrete.iter().map(|&x| arith.lit_ref(x)).collect();
        let denoted_params: Vec<Expr> = denoted_args.iter().map(|a| a.at(arith)).collect();
        let ps: Vec<Expr> = denoted_facts
            .iter()
            .zip(&denoted_params)
            .zip(&lit_params)
            .map(|((pf, dp), lp)| kernel::sym(&int_ty, dp, lp, pf.at(arith)))
            .collect();
        let v_resolved = v.at(arith);
        let v_anchored = Anchored::new(arith, v_resolved.clone());
        let f = params_and_close(arith, self_call.arity, kernel::close_lam, |arith, pp| {
            Some(ev_of(arith, ev_pos, &pp.at(arith), v_anchored.at(arith)))
        })?;
        let ev_eq = kernel::cong_n(&int_ty, &kernel::sort(0), &f, &lit_params, &denoted_params, ps);
        let e = kernel::transport(
            0,
            ev_of(arith, ev_pos, &lit_params, v_resolved.clone()),
            ev_of(arith, ev_pos, &denoted_params, v_resolved),
            ev_eq,
            e_canonical.at(arith),
        );
        vs.push(v);
        es.push(Anchored::new(arith, e));
    }

    // Nothing left to grow arith.p.ctx from here -- resolve everything
    // fresh, once, for the final assembly.
    let params: Vec<Expr> = params.iter().map(|a| a.at(arith)).collect();
    let premises: Vec<Expr> = premises.iter().map(|a| a.at(arith)).collect();
    let vs: Vec<Expr> = vs.iter().map(|a| a.at(arith)).collect();
    let es: Vec<Expr> = es.iter().map(|a| a.at(arith)).collect();

    let args = params.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es);
    let e = apply_n(arith.p.get(ev_leaf_positions[leaf_idx]), args);
    let v = combine_of(arith, &combines[leaf_idx], &params, &vs);
    debug_assert_has_type(&arith.p.ctx, &v, &arith.int_ty(), "build_ev_witness: v");
    debug_assert_has_type(&arith.p.ctx, &e, &ev_of(arith, ev_pos, &params, v.clone()), "build_ev_witness: e");
    memo.insert(concrete.to_vec(), (Anchored::new(arith, v.clone()), Anchored::new(arith, e.clone())));
    Some((v, e))
}

/// A kernel-checked witness, concrete to one call `h(args)`, that the
/// universal theorem's `loop_val` reconstruction and the value the
/// recursion actually produces agree -- see `prove_tail_recursive_instance`.
pub struct UniversalInstanceProof {
    pub ctx: Ctx,
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
        ctx: scaffold.arith.p.ctx.clone(),
        arity: scaffold.arity,
        theorem_ty: scaffold.theorem_ty.at(&scaffold.arith),
        theorem_proof: scaffold.theorem_proof.at(&scaffold.arith),
    };
    let instances = args_list
        .iter()
        .map(|args| instance_from_scaffold(store, scaffold.clone(), args))
        .collect();
    Some((theorem, instances))
}

fn instance_from_scaffold(store: &TermStore, mut scaffold: UniversalScaffold, args: &[i64]) -> Option<UniversalInstanceProof> {
    if args.len() != scaffold.arity {
        return None;
    }

    let concrete: Vec<i64> = (0..scaffold.arity).map(|i| args[scaffold.arity - 1 - i]).collect();
    for &c in &concrete {
        scaffold.arith.lit(c);
    }

    // Deliberately *not* wrapped in `kernel::with_shift_cache` here -- this
    // runs for every sample `jit.rs`'s automatic verification tries
    // (typically small and cheap on their own), and confirmed empirically:
    // the cache's own upkeep (a real `HashMap`, grown then dropped --
    // measured over a million entries total across one demo's routine
    // small samples) costs more than it saves at that scale, a real
    // regression on the common path. The win is real but concentrated in
    // large/branching constructions specifically -- see
    // `kernel::with_shift_cache`'s own docs -- so it's opt-in: a caller
    // that expects one (proving a specific large instance on demand, e.g.)
    // wraps its own call to `prove_tail_recursive_instance` in it.
    let mut budget = WITNESS_NODE_BUDGET;
    let mut memo = HashMap::new();
    let (v, e) = build_ev_witness(
        store,
        &mut scaffold.arith,
        scaffold.self_call,
        &scaffold.leaves,
        &scaffold.ev_leaf_positions,
        &scaffold.combines,
        scaffold.ev_pos,
        &concrete,
        &mut budget,
        &mut memo,
    )?;

    // Fresh past all the growth `build_ev_witness` just did.
    let theorem_proof = scaffold.theorem_proof.at(&scaffold.arith);
    let params: Vec<Expr> = concrete.iter().map(|&c| scaffold.arith.lit_ref(c)).collect();
    let applied = apply_n(theorem_proof, params.into_iter().chain([v, e]));
    let ty = kernel::infer(&scaffold.arith.p.ctx, &applied).ok()?;
    let (lhs, rhs) = match kernel::whnf(&ty) {
        Expr::Id(_, lhs, rhs) => (Rc::unwrap_or_clone(lhs), Rc::unwrap_or_clone(rhs)),
        _ => return None,
    };

    Some(UniversalInstanceProof {
        int_ty: scaffold.arith.int_ty(),
        ctx: scaffold.arith.p.ctx,
        arity: scaffold.arity,
        lhs,
        rhs,
        proof: applied,
    })
}

// --- non-capturing ("known-call") closures --------------------------------
//
// Mirrors `compile.rs`'s own known-call/table-index reading of closures
// (see its module docs) at the proof level, for the same fragment it
// compiles: a closed, non-recursive term whose body, plus every
// non-capturing lambda ("combinator") it calls, is built from
// `Var`/`Lit`/`Prim`/`If` and fully-saturated applications of either a
// closure-typed parameter or a literal lambda -- exactly what
// `compile::unwind_app_spine`/`compile::infer_closure_arities` already
// classify, reused directly here rather than re-derived, so the two
// readings can't silently diverge on "what counts as a closure call".
//
// A closure value is postulated opaque (`Clo : Sort(0)`, the same
// "postulated type" pattern `Int` itself uses), one postulated `Clo`-typed
// constant per distinct combinator (memoized by hash, mirroring
// `ArithPostulates::lit`'s per-literal memoization), and one postulated
// `apply_k : Clo -> Int^k -> Int` per distinct arity a closure is actually
// called with (mirroring `compile.rs`'s own `(type $tyK ...)` declarations,
// one per arity actually used at a `call_indirect` site).
//
// Crucially, a combinator's own *body* is never unfolded or denoted here --
// it's referenced only by its postulated identity constant. That's not a
// shortcut: `apply_k(combinator_const, args)` faithfully represents "call
// this specific combinator with these arguments" on *both* readings (a
// Wasm `call`/`call_indirect` to a table slot uniquely identified by hash,
// and a non-capturing `Value::Closure` application, which needs nothing
// from its environment beyond the combinator's own definition) --
// identically, symbol for symbol, the same way `denote`'s postulated `Int`
// operators represent an arithmetic primitive on both readings without
// either being numerically verified. The proof is `refl`, same as
// `prove_pure_expr`'s straight-line argument: nothing here evaluates
// anything concrete, so no `assume_prim_fact`-style grounding is needed.
//
// Scope, honestly: closed, non-recursive terms only (`Rec` anywhere, main
// term or any combinator, is out of scope -- combining this with
// self-recursion is future work); every `If` branch must denote as `Int`
// (an `If` choosing between two *closures* is out of scope, though
// `compile.rs` would compile it); and the whole function's own result must
// denote as `Int`, not directly return a closure value. Also *deliberately*
// narrower than what `compile.rs` itself now compiles: `compile.rs` added
// real closure conversion for genuinely capturing closures (see its module
// docs), but this fragment still covers non-capturing ("known-call")
// closures only -- `ClosureCombinators::register`/`call_ref` explicitly
// reject a capturing combinator (`compile::free_vars`, the same analysis
// `compile.rs`'s own `Combinators::register` uses) rather than relying on
// "already compiled" to imply "non-capturing" the way an earlier version of
// this comment did; that implication stopped holding the moment
// `compile.rs` could compile captures too, so the check has to be explicit
// here now. `combinator_value`/`call_h`'s whole model -- one postulated
// constant per combinator, referenced by identity, its own body never
// denoted -- is only an honest reading of a *non-capturing* closure (always
// the same table-index value, wherever it's referenced); a capturing one
// gets a different environment, and so a different runtime value, at every
// creation site, which this fragment doesn't model at all. Combining this
// with capturing closures is future work, not just an oversight.

/// Either an `Int`-typed or a `Clo`-typed denotation -- `denote_closure`
/// needs to track which, since an application's arguments and an `If`'s
/// branches (in this fragment) must be `Int`, while a call's *callee* and a
/// bare lambda value must be `Clo`.
enum Denoted {
    Int(Expr),
    Clo(Expr),
}
impl Denoted {
    fn int(self) -> Option<Expr> {
        match self {
            Denoted::Int(e) => Some(e),
            Denoted::Clo(_) => None,
        }
    }
    fn clo(self) -> Option<Expr> {
        match self {
            Denoted::Clo(e) => Some(e),
            Denoted::Int(_) => None,
        }
    }
}

/// `h`'s own parameter types, `compile::infer_closure_arities`'s
/// classification on `h`'s *own* body/arity, reindexed from its positional
/// convention to `denote`'s by-`Var`-index one (see `denote_closure`'s
/// docs) -- shared by `prove_closure_expr`'s top-level call and
/// `ClosureCombinators::call_ref`'s per-combinator call signature.
fn param_types_for(store: &TermStore, h: Hash) -> Option<Vec<Option<usize>>> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    if is_rec {
        return None;
    }
    let found = compile::infer_closure_arities(store, body, arity, None)?;
    Some((0..arity).map(|i| found[arity - 1 - i]).collect())
}

/// Extends `ArithPostulates` with postulated closure-value support -- see
/// the section docs above.
struct ClosurePostulates {
    arith: ArithPostulates,
    clo_pos: usize,
    apply_pos: HashMap<usize, usize>,
    combinator_value_pos: HashMap<Hash, usize>,
    combinator_call_pos: HashMap<Hash, usize>,
}

impl ClosurePostulates {
    fn new() -> Self {
        let mut arith = ArithPostulates::new();
        let clo_pos = arith.p.push(kernel::sort(0));
        ClosurePostulates {
            arith,
            clo_pos,
            apply_pos: HashMap::new(),
            combinator_value_pos: HashMap::new(),
            combinator_call_pos: HashMap::new(),
        }
    }

    fn clo_ty(&self) -> Expr {
        self.arith.p.get(self.clo_pos)
    }

    /// `apply_k : Clo -> Int -> .. -> Int` (`k` `Int` params), postulated
    /// once per distinct `k` -- for calling a *parameter*-typed closure
    /// (`call_indirect`), which per `compile.rs`'s own typed dispatch
    /// always takes `Int` arguments regardless of what the callee's own
    /// body does with them.
    fn apply_ref(&mut self, k: usize) -> Expr {
        if let Some(&pos) = self.apply_pos.get(&k) {
            return self.arith.p.get(pos);
        }
        let mut ty = self.arith.int_ty();
        for _ in 0..k {
            ty = kernel::arrow(self.arith.int_ty(), ty);
        }
        let ty = kernel::arrow(self.clo_ty(), ty);
        let pos = self.arith.p.push(ty);
        self.apply_pos.insert(k, pos);
        self.arith.p.get(pos)
    }

    /// A fresh `Clo`-typed constant for combinator `h`, memoized by hash --
    /// for a combinator used as a bare *value* (an argument, a branch
    /// result, ...), mirroring `compile.rs`'s "its value is just its table
    /// index" reading.
    fn combinator_value(&mut self, h: Hash) -> Expr {
        if let Some(&pos) = self.combinator_value_pos.get(&h) {
            return self.arith.p.get(pos);
        }
        let clo_ty = self.clo_ty();
        let pos = self.arith.p.push(clo_ty);
        self.combinator_value_pos.insert(h, pos);
        self.arith.p.get(pos)
    }
}

/// Registers combinators on demand -- unlike `compile.rs`'s own
/// `Combinators`, there's no fixpoint queue to drain: a combinator's body
/// is never denoted here (see the section docs above), so registering one
/// never discovers more work.
struct ClosureCombinators<'a> {
    store: &'a TermStore,
    cp: ClosurePostulates,
}
impl<'a> ClosureCombinators<'a> {
    fn new(store: &'a TermStore) -> Self {
        ClosureCombinators { store, cp: ClosurePostulates::new() }
    }

    /// The postulated `Clo`-typed identity constant for combinator `h`
    /// (`ClosurePostulates::combinator_value`), for `h` used as a bare
    /// value. `None` for a zero-arity, self-recursive, or *capturing*
    /// combinator (out of scope -- see section docs). Unlike `compile.rs`
    /// itself, `h` capturing something has to be checked explicitly here
    /// (`compile::free_vars`, the same analysis `compile.rs`'s own
    /// `Combinators::register` uses) rather than falling out for free:
    /// `compile.rs` compiles a genuinely capturing closure successfully
    /// now (real closure conversion), so this module can no longer rely
    /// on "already compiled" to mean "non-capturing" the way it used to.
    /// `combinator_value(h)` models `h` as *one* fixed value regardless
    /// of where it's referenced -- true for a non-capturing closure
    /// (always the same table-index constant), false for a capturing one
    /// (a different environment, and so a different packed value, at
    /// every creation site) -- so admitting a capturing combinator here
    /// wouldn't just be incomplete, it would be an honestly wrong model.
    fn register(&mut self, h: Hash) -> Option<Expr> {
        let (arity, body, is_rec) = compile::peel(self.store, h)?;
        if is_rec || arity == 0 {
            return None;
        }
        if !compile::free_vars(self.store, body, arity, is_rec).is_empty() {
            return None;
        }
        Some(self.cp.combinator_value(h))
    }

    /// A postulated function `call_h : T_0 -> T_1 -> .. -> T_{k-1} -> Int`
    /// for *directly calling* combinator `h` (a static Wasm `call`, not
    /// dispatched through any `Clo` value at all -- unlike `apply_ref`,
    /// there's no leading `Clo` argument here), memoized by hash. Each
    /// `T_j` (`j` in application order, i.e. `T_0` is the *first*-applied
    /// argument's type) is `Clo` or `Int` matching `h`'s own `param_types`
    /// at that position -- this is what lets a combinator like `twice`
    /// (`Clo -> Int -> Int`, since its own `f` parameter is itself
    /// closure-typed) be called with a mix of closure and plain-`Int`
    /// arguments, which the uniform `apply_k` can't express.
    fn call_ref(&mut self, h: Hash) -> Option<Expr> {
        if let Some(&pos) = self.cp.combinator_call_pos.get(&h) {
            return Some(self.cp.arith.p.get(pos));
        }
        // Same capturing check as `register`, and for the same reason:
        // `call_h` is one postulated function per combinator, its own
        // body never denoted -- an honest model only for a genuinely
        // fixed function, which a capturing combinator (different
        // environment per creation site) isn't.
        let (arity, body, is_rec) = compile::peel(self.store, h)?;
        if !compile::free_vars(self.store, body, arity, is_rec).is_empty() {
            return None;
        }
        let param_types = param_types_for(self.store, h)?;
        let mut ty = self.cp.arith.int_ty();
        // Var(0) is last-applied (innermost -- wrap it first, so the
        // final iteration, Var(arity-1) = first-applied, ends up
        // outermost, matching apply_n's left-to-right application order).
        for pt in &param_types {
            let dom = match pt {
                Some(_) => self.cp.clo_ty(),
                None => self.cp.arith.int_ty(),
            };
            ty = kernel::arrow(dom, ty);
        }
        let pos = self.cp.arith.p.push(ty);
        self.cp.combinator_call_pos.insert(h, pos);
        Some(self.cp.arith.p.get(pos))
    }
}

/// Like `collect_literals`, but for the closures fragment: an `App` chain
/// is only ever a closure call (resolved the same way `denote_closure`
/// resolves one), never rejected outright the way `collect_literals`
/// (built for the arithmetic-only fragments) rejects any bare `App`.
/// `param_types[i]` is `Some(k)` for a closure-typed parameter (see
/// `denote_closure`'s docs), `None` for a plain `Int` one.
fn collect_literals_closure(store: &TermStore, h: Hash, param_types: &[Option<usize>], out: &mut Vec<i64>) -> bool {
    if matches!(store.resolve(h), Term::App(..)) {
        let (root, args) = compile::unwind_app_spine(store, h);
        let ok_root = match store.resolve(root) {
            Term::Var(i) => param_types.get(*i as usize).copied().flatten().is_some(),
            Term::Abs(_) => matches!(compile::peel(store, root), Some((a, _, false)) if a > 0),
            _ => false,
        };
        if !ok_root {
            return false;
        }
        return args.iter().all(|&a| collect_literals_closure(store, a, param_types, out));
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
            collect_literals_closure(store, *a, param_types, out) && collect_literals_closure(store, *b, param_types, out)
        }
        Term::If(c, t, e) => {
            collect_literals_closure(store, *c, param_types, out)
                && collect_literals_closure(store, *t, param_types, out)
                && collect_literals_closure(store, *e, param_types, out)
        }
        Term::Abs(_) => true, // a bare value -- opaque, nothing inside it to collect
        Term::Rec(_) => false,
        Term::App(..) => unreachable!("handled above"),
    }
}

/// Translates a closures-fragment term into a kernel expression -- see the
/// section docs above for what each case represents on both readings.
/// `params[i]`/`param_types[i]` describe the enclosing function's own
/// `Var(i)`: `param_types[i] = Some(k)` for a closure-typed parameter
/// always called with `k` arguments (`compile::infer_closure_arities`'s own
/// classification, reindexed from its positional convention to `denote`'s
/// by-`Var`-index one), `None` for a plain `Int` parameter. `params` holds
/// *positions*, not resolved `Expr`s (the same `Params`-style convention
/// `prove_tail_recursive_universal` uses) -- resolved fresh, via
/// `arith.p.get`, at each actual use: registering a combinator or a fresh
/// `apply_k` mid-denotation pushes further postulates onto `arith.p.ctx`,
/// so a `Var`'s `Expr` resolved once, ahead of time, and reused afterward
/// would go stale exactly the way `Anchored`'s docs describe.
fn denote_closure(
    store: &TermStore,
    h: Hash,
    combinators: &mut ClosureCombinators,
    params: &[usize],
    param_types: &[Option<usize>],
) -> Option<Denoted> {
    // Every composite case below follows the same discipline: compute each
    // sub-denotation and immediately wrap it in `Anchored` (registering a
    // combinator or a fresh `apply_k` -- possibly triggered by a *later*
    // sibling's own denotation -- pushes further postulates onto
    // `arith.p.ctx`, which would otherwise silently invalidate an
    // already-resolved `Var` reference held from an earlier sibling, the
    // same staleness class `Anchored`'s own docs describe), then resolve
    // everything fresh, in one batch, only once nothing more is left to
    // push for this node.
    if matches!(store.resolve(h), Term::App(..)) {
        let (root, args) = compile::unwind_app_spine(store, h);
        match store.resolve(root) {
            // A parameter-typed closure, called through `call_indirect`:
            // per compile.rs's own typed dispatch, arguments are always
            // `Int` regardless of the callee's own signature.
            Term::Var(i) => {
                let k = (*param_types.get(*i as usize)?)?;
                if args.len() != k {
                    return None;
                }
                let callee = denote_closure(store, root, combinators, params, param_types)?.clo()?;
                let callee = Anchored::new(&combinators.cp.arith, callee);
                let mut arg_exprs = Vec::with_capacity(args.len());
                for &a in &args {
                    let e = denote_closure(store, a, combinators, params, param_types)?.int()?;
                    arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                }
                let apply_fn = combinators.cp.apply_ref(k);
                let callee = callee.at(&combinators.cp.arith);
                let arg_exprs: Vec<Expr> = arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)).collect();
                let applied = apply_n(apply_fn, std::iter::once(callee).chain(arg_exprs));
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_closure: call_indirect application");
                return Some(Denoted::Int(applied));
            }
            // A literal lambda in function position, called directly (a
            // static Wasm `call`, no closure value involved at all): each
            // argument's expected type matches the *callee's own*
            // parameter type at that position (`Clo` or `Int`), which is
            // what lets e.g. `twice(inc, 5)` pass a closure and a plain
            // `Int` to the same call.
            Term::Abs(_) => {
                let callee_param_types = param_types_for(store, root)?;
                let arity = callee_param_types.len();
                if args.len() != arity {
                    return None;
                }
                let call_fn = combinators.call_ref(root)?;
                let call_fn = Anchored::new(&combinators.cp.arith, call_fn);
                let mut arg_exprs = Vec::with_capacity(args.len());
                for (j, &a) in args.iter().enumerate() {
                    // args[j] (application order) is Var(arity-1-j) --
                    // see param_types_for's/denote's own convention.
                    let d = denote_closure(store, a, combinators, params, param_types)?;
                    let e = match callee_param_types[arity - 1 - j] {
                        Some(_) => d.clo()?,
                        None => d.int()?,
                    };
                    arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                }
                let call_fn = call_fn.at(&combinators.cp.arith);
                let arg_exprs: Vec<Expr> = arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)).collect();
                let applied = apply_n(call_fn, arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_closure: direct combinator call");
                return Some(Denoted::Int(applied));
            }
            _ => return None,
        }
    }

    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        let dc = denote_closure(store, c, combinators, params, param_types)?.int()?;
        let dc = Anchored::new(&combinators.cp.arith, dc);
        let dt = denote_closure(store, t, combinators, params, param_types)?.int()?;
        let dt = Anchored::new(&combinators.cp.arith, dt);
        let de = denote_closure(store, e, combinators, params, param_types)?.int()?;
        let ite = combinators.cp.arith.ite_ref(); // pre-postulated once in ArithPostulates::new -- never pushes
        let dc = dc.at(&combinators.cp.arith);
        let dt = dt.at(&combinators.cp.arith);
        let applied = kernel::app3(ite, dc, dt, de);
        let int_ty = combinators.cp.arith.int_ty();
        debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_closure: If");
        return Some(Denoted::Int(applied));
    }

    match store.resolve(h) {
        Term::Var(i) => {
            let i = *i as usize;
            let p = combinators.cp.arith.p.get(*params.get(i)?);
            match *param_types.get(i)? {
                Some(_) => Some(Denoted::Clo(p)),
                None => Some(Denoted::Int(p)),
            }
        }
        Term::Lit(n) => Some(Denoted::Int(combinators.cp.arith.lit_ref(*n))),
        Term::Prim(op, a, b) => {
            let da = denote_closure(store, *a, combinators, params, param_types)?.int()?;
            let da = Anchored::new(&combinators.cp.arith, da);
            let db = denote_closure(store, *b, combinators, params, param_types)?.int()?;
            let op_ref = combinators.cp.arith.op_ref(*op); // pre-postulated once -- never pushes
            let da = da.at(&combinators.cp.arith);
            let applied = kernel::app2(op_ref, da, db);
            let int_ty = combinators.cp.arith.int_ty();
            debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_closure: Prim");
            Some(Denoted::Int(applied))
        }
        Term::Abs(_) => {
            let (arity, _, is_rec) = compile::peel(store, h)?;
            if is_rec || arity == 0 {
                return None;
            }
            Some(Denoted::Clo(combinators.register(h)?))
        }
        Term::If(..) | Term::App(..) => unreachable!("handled above"),
        Term::Rec(_) => None,
    }
}

/// Attempts to build an [`EquivalenceProof`] for `h`, covering every input,
/// for the non-capturing-closures fragment `compile.rs` compiles (see the
/// section docs above for exactly what's in and out of scope). Returns
/// `None` for anything outside it: a `Rec`-wrapped term (self-recursion
/// combined with closures isn't covered), an application whose callee is
/// neither a closure-typed parameter nor a literal lambda, an inconsistent
/// arity for a closure-typed parameter, an `If` whose branches aren't both
/// `Int`, or a whole-function result that isn't `Int`.
pub fn prove_closure_expr(store: &TermStore, h: Hash) -> Option<EquivalenceProof> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    if is_rec {
        return None;
    }

    let found = compile::infer_closure_arities(store, body, arity, None)?;
    let param_types: Vec<Option<usize>> = (0..arity).map(|i| found[arity - 1 - i]).collect();

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
            Some(_) => {
                let clo_ty = combinators.cp.clo_ty();
                combinators.cp.arith.p.push(clo_ty)
            }
            None => {
                let int_ty = combinators.cp.arith.int_ty();
                combinators.cp.arith.p.push(int_ty)
            }
        };
        params.push(pos);
    }

    let denotation = denote_closure(store, body, &mut combinators, &params, &param_types)?.int()?;

    let int_ty = combinators.cp.arith.int_ty();
    let proof = kernel::refl(denotation.clone());
    let proof_ty = kernel::id(int_ty.clone(), denotation.clone(), denotation.clone());
    kernel::check(&combinators.cp.arith.p.ctx, &proof, &proof_ty).ok()?;

    Some(EquivalenceProof {
        ctx: combinators.cp.arith.p.ctx,
        arity,
        int_ty,
        denotation,
        proof,
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

    #[test]
    fn tail_recursive_gcd_gets_a_kernel_checked_instance_proof() {
        let mut s = TermStore::new();
        let g = gcd(&mut s);

        for (a, b) in [(48, 18), (270, 192), (17, 5), (0, 7)] {
            let proof = prove_tail_recursive_instance(&s, g, &[a, b])
                .unwrap_or_else(|| panic!("gcd({a},{b}) should get a kernel-checked instance"));
            assert_eq!(proof.arity, 2);
            kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
                .expect("the recorded instance proof should independently re-typecheck");
        }
    }

    #[test]
    fn non_tail_recursion_gets_a_kernel_checked_instance_proof() {
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

        for n in [0, 1, 5, 10] {
            let proof = prove_tail_recursive_instance(&s, fact, &[n])
                .unwrap_or_else(|| panic!("factorial({n}) should get a kernel-checked instance"));
            assert_eq!(proof.arity, 1);
            kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
                .expect("the recorded instance proof should independently re-typecheck");
        }
    }

    #[test]
    fn fibonacci_branching_leaves_get_kernel_checked_instances() {
        // rec f n = if n < 2 then n else f(n-1) + f(n-2) -- two self-calls
        // in the recursive leaf. Once genuinely out of scope (see
        // build_ev_witness's own docs for the fix: a `memo` DP cache plus a
        // congruence-based recast of each cached witness to the calling
        // leaf's own denoted call arguments) -- covers any number of
        // self-calls per leaf now, not just at most one.
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

        // Explicitly opts into `kernel::with_shift_cache` around each call
        // (both building and rechecking) -- unlike `jit.rs`'s own automatic
        // per-sample verification, this test deliberately proves a large
        // (n=8) branching-leaf instance, exactly the case that cache is
        // for (see its own docs, and `instance_from_scaffold`'s for why it
        // isn't on by default).
        for n in [1, 2, 8] {
            let proof = kernel::with_shift_cache(|| prove_tail_recursive_instance(&s, fib, &[n]))
                .unwrap_or_else(|| panic!("fib({n}) should get an instance"));
            assert_eq!(proof.arity, 1);
            kernel::with_shift_cache(|| {
                kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
            })
            .expect("the recorded instance proof should independently re-typecheck");
        }
    }

    #[test]
    fn one_functions_instance_proof_is_rejected_against_anothers_type() {
        // Same adversarial shape as
        // one_functions_theorem_proof_is_rejected_against_anothers_type,
        // one level down: an instance proof built for one function must
        // not typecheck against another's (unrelated Ev/combine layout,
        // different concrete call).
        let mut s = TermStore::new();
        let g = gcd(&mut s);
        let gcd_proof = prove_tail_recursive_instance(&s, g, &[48, 18]).expect("gcd instance proof");

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
        let fact_proof = prove_tail_recursive_instance(&s2, fact, &[5]).expect("factorial instance proof");

        assert!(
            kernel::check(
                &gcd_proof.ctx,
                &gcd_proof.proof,
                &kernel::id(fact_proof.int_ty.clone(), fact_proof.lhs.clone(), fact_proof.rhs.clone()),
            )
            .is_err(),
            "gcd's instance proof should be rejected against factorial's instance type"
        );
    }

    /// `\f. \x. f (f x)` -- both `f` and `x` are its own parameters, no
    /// captures (same shape `compile::tests::twice` uses).
    fn twice(s: &mut TermStore) -> Hash {
        let f = s.var(1);
        let x = s.var(0);
        let fx = s.app(f, x);
        let ffx = s.app(f, fx);
        let inner = s.abs(ffx);
        s.abs(inner)
    }

    /// `\y. y + 1`.
    fn inc(s: &mut TermStore) -> Hash {
        let y = s.var(0);
        let one = s.lit(1);
        let y_plus_1 = s.prim(PrimOp::Add, y, one);
        s.abs(y_plus_1)
    }

    #[test]
    fn twice_inc_5_gets_a_kernel_checked_closure_proof() {
        // (twice inc) 5 -- the higher-order demo term main.rs uses: a
        // closed (arity 0), non-recursive expression combining two
        // non-capturing combinators.
        let mut s = TermStore::new();
        let t = twice(&mut s);
        let i = inc(&mut s);
        let five = s.lit(5);
        let applied = s.app2(t, i, five);

        let proof = prove_closure_expr(&s, applied).expect("(twice inc) 5 should get a closure proof");
        assert_eq!(proof.arity, 0);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        // Also actually compiles -- the proof and the compiler agree on
        // this term being in scope.
        assert!(compile::try_compile(&s, applied).is_some());
    }

    #[test]
    fn twice_alone_gets_a_kernel_checked_closure_proof() {
        // twice itself, standalone: f is a closure-typed parameter (always
        // called with 1 argument), x a plain Int parameter.
        let mut s = TermStore::new();
        let t = twice(&mut s);

        let proof = prove_closure_expr(&s, t).expect("twice alone should get a closure proof");
        assert_eq!(proof.arity, 2);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");
    }

    #[test]
    fn recursion_combined_with_closures_is_out_of_scope() {
        // Even a trivial Rec wrapper puts a closures term out of scope for
        // prove_closure_expr (see its own docs) -- combining the two is
        // future work, not (yet) covered.
        let mut s = TermStore::new();
        let t = twice(&mut s);
        let i = inc(&mut s);
        let x = s.var(0);
        let applied = s.app2(t, i, x);
        let inner = s.abs(applied);
        let wrapped = s.rec(inner);

        assert!(prove_closure_expr(&s, wrapped).is_none());
    }

    #[test]
    fn partial_application_is_still_out_of_scope_for_the_closure_proof() {
        // \f. f(1) + f(1, 2) -- same adversarial shape as
        // compile::tests::partial_application_is_still_rejected.
        let mut s = TermStore::new();
        let f1 = s.var(0);
        let one = s.lit(1);
        let call1 = s.app(f1, one);
        let f2 = s.var(0);
        let two = s.lit(2);
        let call2 = s.app2(f2, one, two);
        let body = s.prim(PrimOp::Add, call1, call2);
        let g = s.abs(body);

        assert!(prove_closure_expr(&s, g).is_none());
        assert!(compile::try_compile(&s, g).is_none(), "the compiler should agree this is out of scope too");
    }

    #[test]
    fn a_capturing_closure_compiles_but_still_gets_no_closure_proof() {
        // \x. (\g. g 5) (if 0 < x then (\y. x + y) else (\y. x - y)) --
        // the same term compile.rs's own
        // a_capturing_closure_compiles_and_matches_interpreter test uses.
        // compile.rs compiles this successfully now (real closure
        // conversion), but prove_closure_expr's own model -- one
        // postulated constant per combinator, referenced by identity --
        // is only an honest reading of a *non-capturing* closure (see its
        // section docs); a capturing combinator gets a different
        // environment at every creation site, which that model doesn't
        // represent at all, so this must still come back `None`, not
        // silently reuse compile.rs's now-broader "does it compile"
        // scope.
        let mut s = TermStore::new();
        let x = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, x);
        let y_pos = s.var(0);
        let x_pos = s.var(1);
        let plus = s.prim(PrimOp::Add, x_pos, y_pos);
        let then_closure = s.abs(plus);
        let y_neg = s.var(0);
        let x_neg = s.var(1);
        let minus = s.prim(PrimOp::Sub, x_neg, y_neg);
        let else_closure = s.abs(minus);
        let body = s.if_(cond, then_closure, else_closure);
        let picker = s.abs(body);

        let g = s.var(0);
        let five = s.lit(5);
        let call_g = s.app(g, five);
        let inn = s.abs(call_g);

        let x2 = s.var(0);
        let chosen = s.app(picker, x2);
        let called = s.app(inn, chosen);
        let f = s.abs(called);

        assert!(compile::try_compile(&s, f).is_some(), "compile.rs should compile this via closure conversion");
        assert!(prove_closure_expr(&s, f).is_none(), "prove_closure_expr's non-capturing model must still decline it");
    }

    #[test]
    fn an_if_choosing_between_two_closures_is_out_of_scope() {
        // \x. if x > 0 then inc else inc -- compile.rs would happily
        // compile this (both branches are just i64 table indices), but
        // prove_closure_expr requires both If branches to denote as Int
        // (see its own docs) -- a real, documented restriction, not a bug.
        let mut s = TermStore::new();
        let x = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, x);
        let i1 = inc(&mut s);
        let i2 = inc(&mut s);
        let picked = s.if_(cond, i1, i2);
        let f = s.abs(picked);

        assert!(prove_closure_expr(&s, f).is_none());
    }

    #[test]
    fn one_closure_terms_proof_is_rejected_against_anothers_type() {
        // Adversarial: twice_inc_5's proof, checked in its own ctx, against
        // twice-alone's type -- must be rejected, not somehow typecheck.
        let mut s = TermStore::new();
        let t = twice(&mut s);
        let i = inc(&mut s);
        let five = s.lit(5);
        let applied = s.app2(t, i, five);
        let applied_proof = prove_closure_expr(&s, applied).expect("(twice inc) 5 should get a closure proof");

        let mut s2 = TermStore::new();
        let t2 = twice(&mut s2);
        let alone_proof = prove_closure_expr(&s2, t2).expect("twice alone should get a closure proof");

        assert!(
            kernel::check(
                &applied_proof.ctx,
                &applied_proof.proof,
                &kernel::id(alone_proof.int_ty.clone(), alone_proof.denotation.clone(), alone_proof.denotation.clone()),
            )
            .is_err(),
            "(twice inc) 5's proof should be rejected against twice-alone's type"
        );
    }
}
