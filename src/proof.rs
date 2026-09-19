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
//! Scope: every `If` on the way to a leaf (i.e. one `classify_tree` pulls
//! into the [`DecisionTree`] itself, gating which leaf is reached) must
//! have a direct comparison as its condition (`compile_cond` in
//! `compile.rs` requires that too, and gating above relies on comparisons
//! denoting to exactly `0` or `1`); `body` must have at least one leaf
//! with a self-call somewhere in it (otherwise there's no recursion to
//! induct on at all). A leaf's own expression *may* itself contain a
//! further nested `If`, either purely arithmetic (e.g.
//! `n + (if c then 1 else 2)`) or choosing between two `Clo`-typed values
//! (e.g. a self-call argument `f(n-1, if c then g else h)`) --
//! `find_self_calls`/`denote_with_placeholders` recurse into it exactly
//! like a `Prim`, treating it as fully opaque via `ite_ref`/`ite_clo_ref`
//! the same way `denote_closure` already does (no branch is ever resolved
//! concretely at this, the universal, all-inputs level; a self-call
//! inside either branch just becomes one more placeholder of the leaf's
//! `combine` function). `prove_tail_recursive_call` already handles
//! arbitrary branching *and* arbitrary self-call placement on its own (it
//! just follows one concrete path per call, denoting whatever it finds
//! along the way), so neither of those needed widening.

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
    /// Memoized per `(c, t, e)` -- see `assume_ite_fact`, `assume_prim_fact`'s
    /// counterpart for a nested `If` inside a leaf.
    ite_fact_pos: HashMap<(i64, i64, i64), usize>,
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
            ite_fact_pos: HashMap::new(),
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

    /// `assume_prim_fact`'s counterpart for `ite_ref`: postulates (memoized
    /// per `(c, t, e)`) that concretely evaluating a nested `If` at literals
    /// `c`/`t`/`e` yields `eval_concrete`'s own `If` result (`t` if `c != 0`
    /// else `e`) -- needed once a leaf may itself contain a further nested
    /// `If` (see the module docs), since `eval_and_prove` then has to
    /// discharge `app3(ite_ref, ..)` concretely the same way it already
    /// does for a `Prim` application.
    fn assume_ite_fact(&mut self, c: i64, t: i64, e: i64) -> Expr {
        let key = (c, t, e);
        if let Some(&pos) = self.ite_fact_pos.get(&key) {
            return self.p.get(pos);
        }
        let result = if c != 0 { t } else { e };
        self.lit(c);
        self.lit(t);
        self.lit(e);
        self.lit(result);
        let lhs = kernel::app3(self.ite_ref(), self.lit_ref(c), self.lit_ref(t), self.lit_ref(e));
        let rhs = self.lit_ref(result);
        let ty = kernel::id(self.int_ty(), lhs, rhs);
        let pos = self.p.push(ty);
        self.ite_fact_pos.insert(key, pos);
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
/// `param_types` is `Some(..)` only for `build_universal`'s own closure-aware
/// call (see its docs): when present, an `App` that isn't a self-call but
/// *is* a fully-saturated call through a `Clo`-typed parameter (`Var(i)`
/// with `param_types[i] = Some(k)`, `k` arguments) is recursed into (its
/// arguments may still contain literals) instead of rejected outright.
/// `None` (every other caller) keeps the original, closures-blind behavior:
/// any bare `App` fails the whole collection.
fn collect_literals(
    store: &TermStore,
    h: Hash,
    arity: usize,
    self_idx: Option<u32>,
    param_types: Option<&[Option<usize>]>,
    out: &mut Vec<i64>,
) -> bool {
    if let Some(args) = compile::match_self_call(store, h, arity, self_idx) {
        return args
            .iter()
            .all(|&a| collect_literals(store, a, arity, self_idx, param_types, out));
    }
    if let Some(param_types) = param_types
        && matches!(store.resolve(h), Term::App(..))
    {
        let (root, args) = compile::unwind_app_spine(store, h);
        let ok = match store.resolve(root) {
            Term::Var(i) => param_types.get(*i as usize).copied().flatten() == Some(args.len()),
            // A closure created and called right here (see
            // denote_closure_typed's own docs): only the arguments are
            // ever collected from -- a combinator's own body is never
            // denoted regardless of whether it's called, matching
            // collect_literals_closure's identical "opaque, nothing to
            // collect" treatment of a bare Abs/Rec value.
            Term::Abs(_) | Term::Rec(_) => matches!(compile::peel(store, root), Some((a, _, _)) if a > 0),
            _ => false,
        };
        if !ok {
            return false;
        }
        return args.iter().all(|&a| collect_literals(store, a, arity, self_idx, Some(param_types), out));
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
            collect_literals(store, *a, arity, self_idx, param_types, out)
                && collect_literals(store, *b, arity, self_idx, param_types, out)
        }
        Term::If(c, t, e) => {
            collect_literals(store, *c, arity, self_idx, param_types, out)
                && collect_literals(store, *t, arity, self_idx, param_types, out)
                && collect_literals(store, *e, arity, self_idx, param_types, out)
        }
        // A freshly-created closure used as a bare value (not applied here
        // -- see denote_closure_typed's own docs), only when `param_types`
        // says we're in the closures-aware fragment at all (`None` means
        // the plain-arithmetic-only callers, `prove_pure_expr`/
        // `prove_tail_recursive_call`'s shared `setup`, where an `Abs`
        // anywhere is still unconditionally out of scope).
        Term::Abs(_) if param_types.is_some() => true,
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
    if !collect_literals(store, body, arity, self_idx, None, &mut lits) {
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
// through the recursion unchanged or called via `apply_k` within a leaf or
// a self-call argument (`param_types`, the same `Var`-index-keyed
// classification `denote_closure`'s own fragment uses, computed once via
// `compile::infer_closure_arities` on the whole body including self-call
// sites) -- e.g. "iterate a closure `n` times": `rec f n g x = if n<=0
// then x else f(n-1, g, g(x))`. This part needs only `ClosurePostulates`'s
// `Clo` type and `apply_k`, reused directly (`ClosurePostulates:
// Deref<Target = ArithPostulates>` lets this whole pipeline keep calling
// every plain-arithmetic postulate method unchanged). A closure-typed
// self-call argument, or one fed to a closure call, must resolve to a bare
// parameter reference (or, for a plain `Int` one, ordinary arithmetic
// possibly including a closure call) -- an `If` between two closures is
// out of scope here too, same restriction as `denote_closure`'s own.
// Caught a real bug while building this: `ClosurePostulates::apply_ref`'s
// lazy-postulate memoization was designed for `denote_closure`'s own
// usage, where the postulate context only ever grows -- here,
// `params_and_close_typed` repeatedly pushes-then-rolls-back the very same
// scratch space, and `apply_ref`'s *first* call for a given arity, if
// triggered from inside one of those temporary scopes, memoized a
// position that then got rolled back while the memo entry stayed, silently
// going stale. Fixed by pre-pushing every arity the body will ever need,
// once, before any temporary scope gets the chance -- caught immediately by
// `kernel::check`'s own final re-verification (a lambda-domain mismatch),
// not silently accepted, and confirmed by deliberately reintroducing it: a
// dedicated regression test (mixed `Clo`/`Int` parameters, so the bug is
// actually observable) failed the same way before the fix.
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
// directly, not nested inside any self-call's own argument list. Caught
// the *same class* of staleness bug a second time, in a new place:
// `register`/`call_ref`/`pap_ref`, and transitively `mk_env_ref`/`env_ty`
// for a capturing one, are *all* lazily memoized exactly like `apply_ref`,
// and either `denote_closure_typed`'s or `denote_with_placeholders`'s
// first real call (from inside a temporary scope) could trigger any of
// them for the first time just as easily. Since these registrations
// depend only on a combinator's `Hash` and a capture *count* -- never the
// actual parameter *values* -- `prime_closure_postulates` pre-triggers
// every one a self-call argument *or a leaf's own expression* will need
// via a lightweight structural walk (no `params` needed at all, and now
// itself self-call-aware -- matching `find_self_calls`'s own precedence,
// stopping at a self-call occurrence rather than walking into it, since
// that occurrence's own arguments are primed separately), the same
// upfront-priming fix widened to cover closure creation, not just a call
// through a parameter. Also honestly scoped: `eval_and_prove`/
// `build_ev_witness` (the *instance*, per-call specialization) remain
// untouched and still reject `App`/`Abs` outright, so a concrete instance
// proof for either shape still declines -- `kernel_verified` doesn't
// depend on that (see `jit.rs`'s own docs), so this doesn't weaken what
// actually gets verified, only what gets additional, call-specific
// evidence.

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
/// compiles), each leaf an arithmetic expression (`Var`/`Lit`/`Prim`/`If`)
/// that may itself contain any number of self-call occurrences (zero, for
/// a base case; one in tail position, for the old tail-recursion special
/// case; one or more anywhere else, e.g. `f(n-1) + f(n-2)`, including
/// inside a further, purely-arithmetic nested `If`, e.g.
/// `n + (if c then f(n-1) else f(n-2))`) -- `classify_tree` only extracts
/// an `If` that's the *whole* body of some branch into the tree itself;
/// one embedded as a sub-expression of a leaf just stays part of that
/// leaf's own expression, handled by `find_self_calls`/
/// `denote_with_placeholders` the same way a `Prim` is.
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
/// `find_self_calls` cover (a `Clo`-typed nested-`If` value, a
/// non-tail-recursion `Abs`, a free `App`, ...).
fn flatten_tree(store: &TermStore, tree: &DecisionTree, self_call: SelfCall, param_types: &[Option<usize>]) -> Option<Vec<Leaf>> {
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
fn find_self_calls(store: &TermStore, h: Hash, self_call: SelfCall, param_types: &[Option<usize>], out: &mut Vec<Vec<Hash>>) -> bool {
    if let Some(args) = compile::match_self_call(store, h, self_call.arity, Some(self_call.idx)) {
        out.push(args);
        return true;
    }
    if matches!(store.resolve(h), Term::App(..)) {
        let (root, args) = compile::unwind_app_spine(store, h);
        let ok = match store.resolve(root) {
            Term::Var(i) => param_types.get(*i as usize).copied().flatten() == Some(args.len()),
            // A closure created and (fully or partially) called right
            // here -- see `denote_with_placeholders`'s own docs. Recurses
            // into the arguments only, never into the combinator's own
            // body: a genuine self-call occurring *inside* a nested
            // closure's body would need `self_call.idx` shifted by that
            // closure's own arity to still refer to the same absolute
            // position, which `compile::match_self_call`'s unadjusted
            // check can't see -- the combinator's body is opaque here for
            // the same reason it already is to `collect_literals`.
            Term::Abs(_) | Term::Rec(_) => matches!(compile::peel(store, root), Some((a, _, _)) if a > 0),
            _ => false,
        };
        if !ok {
            return false;
        }
        return args.iter().all(|&a| find_self_calls(store, a, self_call, param_types, out));
    }
    match store.resolve(h) {
        Term::Var(_) | Term::Lit(_) => true,
        Term::Prim(_, a, b) => {
            find_self_calls(store, *a, self_call, param_types, out) && find_self_calls(store, *b, self_call, param_types, out)
        }
        // A closure used as a bare value (not applied here) -- opaque,
        // nothing inside it to search for a self-call occurrence, the
        // same reasoning as the App-root case just above.
        Term::Abs(_) => true,
        // A nested `If` (only Int-typed condition/branches -- see
        // `denote_with_placeholders`'s matching arm): recurse into all
        // three the same way `Term::Prim` does, so a self-call inside
        // either branch is still found, in the same left-to-right,
        // depth-first order `denote_with_placeholders` will later walk.
        Term::If(c, t, e) => {
            find_self_calls(store, *c, self_call, param_types, out)
                && find_self_calls(store, *t, self_call, param_types, out)
                && find_self_calls(store, *e, self_call, param_types, out)
        }
        Term::App(..) | Term::Rec(_) => false,
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
/// alike. `params` is `Params`'s own raw
/// positions, same rationale (and same staleness-avoidance) as
/// `denote_closure_typed`'s own docs.
#[allow(clippy::too_many_arguments)]
fn denote_with_placeholders(
    store: &TermStore,
    h: Hash,
    self_call: SelfCall,
    param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[usize],
    placeholders: &[usize],
    next: &mut usize,
) -> Option<Denoted> {
    if compile::match_self_call(store, h, self_call.arity, Some(self_call.idx)).is_some() {
        let v = placeholders.get(*next).map(|&pos| combinators.cp.arith.p.get(pos));
        *next += 1;
        return v.map(Denoted::Int);
    }
    if matches!(store.resolve(h), Term::App(..)) {
        let (root, args) = compile::unwind_app_spine(store, h);
        match store.resolve(root) {
            Term::Var(i) => {
                let k = (*param_types.get(*i as usize)?)?;
                if args.len() != k {
                    return None;
                }
                let callee = denote_with_placeholders(store, root, self_call, param_types, combinators, params, placeholders, next)?.clo()?;
                let callee = Anchored::new(&combinators.cp.arith, callee);
                let mut arg_exprs = Vec::with_capacity(k);
                for &a in &args {
                    let e = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?.int()?;
                    arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                }
                let apply_fn = combinators.cp.apply_ref(k);
                let callee = callee.at(&combinators.cp.arith);
                let arg_exprs: Vec<Expr> = arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)).collect();
                let applied = apply_n(apply_fn, std::iter::once(callee).chain(arg_exprs));
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_with_placeholders: call_indirect application");
                return Some(Denoted::Int(applied));
            }
            // A closure created and (fully or partially) called right
            // here, within the leaf's own expression -- mirrors
            // `denote_closure_typed`'s own `Term::Abs | Term::Rec` case
            // (and, through it, `denote_closure`'s) exactly, including its
            // `combinator_return_type`-gated over-application dispatch,
            // just checking for a self-call occurrence in each argument
            // first.
            Term::Abs(_) | Term::Rec(_) => {
                let callee_param_types = param_types_for(store, root)?;
                let arity = callee_param_types.len();
                if args.len() < arity {
                    let k = args.len();
                    let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
                    let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
                    let pap_fn = combinators.pap_ref(root, k, param_types)?;
                    let pap_fn = Anchored::new(&combinators.cp.arith, pap_fn);
                    let env_expr = if root_captures.is_empty() {
                        None
                    } else {
                        let e = build_env_expr(combinators, &root_captures, params, param_types)?;
                        Some(Anchored::new(&combinators.cp.arith, e))
                    };
                    let mut arg_exprs = Vec::with_capacity(k);
                    for (j, &a) in args.iter().enumerate() {
                        let d = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?;
                        let e = match callee_param_types[arity - 1 - j] {
                            Some(_) => d.clo()?,
                            None => d.int()?,
                        };
                        arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                    }
                    let pap_fn = pap_fn.at(&combinators.cp.arith);
                    let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                    if let Some(env_expr) = &env_expr {
                        all_args.push(env_expr.at(&combinators.cp.arith));
                    }
                    all_args.extend(arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)));
                    let applied = apply_n(pap_fn, all_args);
                    // Anchored *before* computing `clo_ty(arity - k)`
                    // below: that lookup may itself lazily push a fresh
                    // postulate on this particular arity's first use,
                    // which would otherwise leave `applied` (built just
                    // above from already-`.at()`-reshifted pieces) stale
                    // by the time it's finally compared -- the same
                    // staleness class `Anchored`'s own docs describe, one
                    // step later than usual (escaping a *value*'s own
                    // construction, not a recursive call boundary).
                    let applied = Anchored::new(&combinators.cp.arith, applied);
                    let clo_ty = combinators.cp.clo_ty(arity - k);
                    let applied = applied.at(&combinators.cp.arith);
                    debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &clo_ty, "denote_with_placeholders: partial application");
                    return Some(Denoted::Clo(applied));
                }
                let sat_args = &args[..arity];
                let (c_arity, c_body, c_is_rec) = compile::peel(store, root)?;
                let captures = compile::free_vars(store, c_body, c_arity, c_is_rec);
                let call_fn = combinators.call_ref(root, &captures, param_types)?;
                let call_fn = Anchored::new(&combinators.cp.arith, call_fn);
                let env_expr = if captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &captures, params, param_types)?;
                    Some(Anchored::new(&combinators.cp.arith, e))
                };
                let mut arg_exprs = Vec::with_capacity(arity);
                for (j, &a) in sat_args.iter().enumerate() {
                    let d = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?;
                    let e = match callee_param_types[arity - 1 - j] {
                        Some(_) => d.clo()?,
                        None => d.int()?,
                    };
                    arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                }
                let call_fn = call_fn.at(&combinators.cp.arith);
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.at(&combinators.cp.arith));
                }
                all_args.extend(arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)));
                let sat_applied = apply_n(call_fn, all_args);
                // Anchored *before* `combinator_return_type`'s own
                // `clo_ty(k)` lookup below, same rationale as the partial
                // application case above: that lookup may itself lazily
                // push a fresh postulate, which would otherwise leave
                // `sat_applied` (already fully built) stale by the time
                // it's finally compared.
                let sat_applied = Anchored::new(&combinators.cp.arith, sat_applied);
                let return_ty = combinator_return_type(store, root).unwrap_or(None);
                let returns_clo = return_ty.is_some();
                let sat_ty = match return_ty {
                    Some(k) => combinators.cp.clo_ty(k),
                    None => combinators.cp.arith.int_ty(),
                };
                let sat_applied = sat_applied.at(&combinators.cp.arith);
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &sat_applied, &sat_ty, "denote_with_placeholders: direct combinator call");

                if args.len() == arity {
                    return Some(if returns_clo { Denoted::Clo(sat_applied) } else { Denoted::Int(sat_applied) });
                }

                if !returns_clo {
                    return None; // over-application of a plain Int result: genuinely out of scope
                }
                let extra_args = &args[arity..];
                let sat_applied = Anchored::new(&combinators.cp.arith, sat_applied);
                let mut extra_arg_exprs = Vec::with_capacity(extra_args.len());
                for &a in extra_args {
                    let e = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?.int()?;
                    extra_arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                }
                let apply_fn = combinators.cp.apply_ref(extra_args.len());
                let sat_applied = sat_applied.at(&combinators.cp.arith);
                let extra_arg_exprs: Vec<Expr> = extra_arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)).collect();
                let applied = apply_n(apply_fn, std::iter::once(sat_applied).chain(extra_arg_exprs));
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_with_placeholders: over-application dispatch");
                return Some(Denoted::Int(applied));
            }
            _ => return None,
        }
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
            let da = denote_with_placeholders(store, *a, self_call, param_types, combinators, params, placeholders, next)?.int()?;
            let da = Anchored::new(&combinators.cp.arith, da);
            let db = denote_with_placeholders(store, *b, self_call, param_types, combinators, params, placeholders, next)?.int()?;
            let op_ref = combinators.cp.arith.op_ref(*op);
            let da = da.at(&combinators.cp.arith);
            let applied = kernel::app2(op_ref, da, db);
            let int_ty = combinators.cp.arith.int_ty();
            debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_with_placeholders: Prim");
            Some(Denoted::Int(applied))
        }
        // A freshly-created closure *value*, not (yet) called -- mirrors
        // `denote_closure`'s own value-leaf `Term::Abs | Term::Rec` case.
        Term::Abs(_) => {
            let (arity, body, is_rec) = compile::peel(store, h)?;
            if arity == 0 {
                return None;
            }
            let captures = compile::free_vars(store, body, arity, is_rec);
            let sym = combinators.register(h, &captures, param_types)?;
            if captures.is_empty() {
                return Some(Denoted::Clo(sym));
            }
            let sym = Anchored::new(&combinators.cp.arith, sym);
            let env = build_env_expr(combinators, &captures, params, param_types)?;
            let env_expr = Anchored::new(&combinators.cp.arith, env);
            let sym = sym.at(&combinators.cp.arith);
            let env_expr = env_expr.at(&combinators.cp.arith);
            let applied = kernel::app(sym, env_expr);
            let clo_ty = combinators.cp.clo_ty(arity);
            debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &clo_ty, "denote_with_placeholders: capturing closure value");
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
        Term::If(c, t, e) => {
            let dc = denote_with_placeholders(store, *c, self_call, param_types, combinators, params, placeholders, next)?.int()?;
            let dc = Anchored::new(&combinators.cp.arith, dc);
            let dt = denote_with_placeholders(store, *t, self_call, param_types, combinators, params, placeholders, next)?;
            let dt_is_clo = matches!(dt, Denoted::Clo(_));
            let dt = Anchored::new(&combinators.cp.arith, match dt {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            });
            let de = denote_with_placeholders(store, *e, self_call, param_types, combinators, params, placeholders, next)?;
            let de_is_clo = matches!(de, Denoted::Clo(_));
            // Anchored *before* branching on `dt_is_clo`/`de_is_clo` --
            // `ite_clo_ref`'s lazy first-use postulate push would
            // otherwise invalidate an unanchored `dt`/`de`, the same
            // staleness class `denote_closure`'s identical match guards
            // against (see its own comment).
            let de = Anchored::new(&combinators.cp.arith, match de {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            });
            match (dt_is_clo, de_is_clo) {
                (false, false) => {
                    let ite = combinators.cp.arith.ite_ref();
                    let dc = dc.at(&combinators.cp.arith);
                    let dt = dt.at(&combinators.cp.arith);
                    let de = de.at(&combinators.cp.arith);
                    let applied = kernel::app3(ite, dc, dt, de);
                    let int_ty = combinators.cp.arith.int_ty();
                    debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_with_placeholders: nested If (Int branches)");
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
                    let t_arity = return_type_of(store, *t, self_call.arity, Some(self_call.idx), param_types).flatten()?;
                    let e_arity = return_type_of(store, *e, self_call.arity, Some(self_call.idx), param_types).flatten()?;
                    if t_arity != e_arity {
                        return None;
                    }
                    let ite_clo = combinators.cp.ite_clo_ref(t_arity);
                    let dc = dc.at(&combinators.cp.arith);
                    let dt = dt.at(&combinators.cp.arith);
                    let de = de.at(&combinators.cp.arith);
                    let applied = kernel::app3(ite_clo, dc, dt, de);
                    let clo_ty = combinators.cp.clo_ty(t_arity);
                    debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &clo_ty, "denote_with_placeholders: nested If (Clo branches)");
                    Some(Denoted::Clo(applied))
                }
                _ => None,
            }
        }
        Term::Rec(_) | Term::App(..) => None,
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
/// `params` is `Params`'s own raw positions (`&[usize]`, resolved fresh
/// via `combinators.p.get` at each individual use), not pre-resolved
/// `Expr`s: `register`/`call_ref`/`pap_ref` each may push a fresh
/// postulate on first use (memoized afterward, like `apply_ref`), which
/// would silently invalidate an already-resolved `Expr` held across that
/// push -- the same staleness class `Anchored`'s own docs describe. A
/// bare `Term::Rec` (a self-recursive combinator *nested* inside another
/// one's body) stays out of scope, unlike `denote_closure`'s own fragment
/// -- proving one induction correct while assuming another is a genuinely
/// different, unexplored problem, not attempted here.
fn denote_closure_typed(
    store: &TermStore,
    h: Hash,
    self_call: SelfCall,
    param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[usize],
) -> Option<Denoted> {
    if matches!(store.resolve(h), Term::App(..)) {
        let (root, args) = compile::unwind_app_spine(store, h);
        match store.resolve(root) {
            Term::Var(i) => {
                let k = (*param_types.get(*i as usize)?)?;
                if args.len() != k {
                    return None;
                }
                let callee = denote_closure_typed(store, root, self_call, param_types, combinators, params)?.clo()?;
                let callee = Anchored::new(&combinators.cp.arith, callee);
                let mut arg_exprs = Vec::with_capacity(k);
                for &a in &args {
                    let e = denote_closure_typed(store, a, self_call, param_types, combinators, params)?.int()?;
                    arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                }
                let apply_fn = combinators.cp.apply_ref(k);
                let callee = callee.at(&combinators.cp.arith);
                let arg_exprs: Vec<Expr> = arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)).collect();
                let applied = apply_n(apply_fn, std::iter::once(callee).chain(arg_exprs));
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_closure_typed: call_indirect application");
                return Some(Denoted::Int(applied));
            }
            // A literal lambda -- or a named self-recursive combinator --
            // created and (fully or partially) called right here, in a
            // self-call argument position: mirrors `denote_closure`'s own
            // App-root `Term::Abs | Term::Rec` case exactly (same
            // direct-call/partial-application/over-application 3-way,
            // same `pap_ref`-still-rejects-a-recursive-root narrowing,
            // same `combinator_return_type`-gated over-application
            // dispatch), just against `combinators` directly instead of
            // through a wrapper.
            Term::Abs(_) | Term::Rec(_) => {
                let callee_param_types = param_types_for(store, root)?;
                let arity = callee_param_types.len();
                if args.len() < arity {
                    let k = args.len();
                    let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
                    let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
                    let pap_fn = combinators.pap_ref(root, k, param_types)?;
                    let pap_fn = Anchored::new(&combinators.cp.arith, pap_fn);
                    let env_expr = if root_captures.is_empty() {
                        None
                    } else {
                        let e = build_env_expr(combinators, &root_captures, params, param_types)?;
                        Some(Anchored::new(&combinators.cp.arith, e))
                    };
                    let mut arg_exprs = Vec::with_capacity(k);
                    for (j, &a) in args.iter().enumerate() {
                        let d = denote_closure_typed(store, a, self_call, param_types, combinators, params)?;
                        let e = match callee_param_types[arity - 1 - j] {
                            Some(_) => d.clo()?,
                            None => d.int()?,
                        };
                        arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                    }
                    let pap_fn = pap_fn.at(&combinators.cp.arith);
                    let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                    if let Some(env_expr) = &env_expr {
                        all_args.push(env_expr.at(&combinators.cp.arith));
                    }
                    all_args.extend(arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)));
                    let applied = apply_n(pap_fn, all_args);
                    // Anchored *before* computing `clo_ty(arity - k)`
                    // below -- see `denote_with_placeholders`'s identical
                    // case for the rationale.
                    let applied = Anchored::new(&combinators.cp.arith, applied);
                    let clo_ty = combinators.cp.clo_ty(arity - k);
                    let applied = applied.at(&combinators.cp.arith);
                    debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &clo_ty, "denote_closure_typed: partial application");
                    return Some(Denoted::Clo(applied));
                }
                let sat_args = &args[..arity];
                let (c_arity, c_body, c_is_rec) = compile::peel(store, root)?;
                let captures = compile::free_vars(store, c_body, c_arity, c_is_rec);
                let call_fn = combinators.call_ref(root, &captures, param_types)?;
                let call_fn = Anchored::new(&combinators.cp.arith, call_fn);
                let env_expr = if captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &captures, params, param_types)?;
                    Some(Anchored::new(&combinators.cp.arith, e))
                };
                let mut arg_exprs = Vec::with_capacity(arity);
                for (j, &a) in sat_args.iter().enumerate() {
                    let d = denote_closure_typed(store, a, self_call, param_types, combinators, params)?;
                    let e = match callee_param_types[arity - 1 - j] {
                        Some(_) => d.clo()?,
                        None => d.int()?,
                    };
                    arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                }
                let call_fn = call_fn.at(&combinators.cp.arith);
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.at(&combinators.cp.arith));
                }
                all_args.extend(arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)));
                let sat_applied = apply_n(call_fn, all_args);
                // Anchored *before* `combinator_return_type`'s own
                // `clo_ty(k)` lookup below -- see
                // `denote_with_placeholders`'s identical case for the
                // rationale.
                let sat_applied = Anchored::new(&combinators.cp.arith, sat_applied);
                let return_ty = combinator_return_type(store, root).unwrap_or(None);
                let returns_clo = return_ty.is_some();
                let sat_ty = match return_ty {
                    Some(k) => combinators.cp.clo_ty(k),
                    None => combinators.cp.arith.int_ty(),
                };
                let sat_applied = sat_applied.at(&combinators.cp.arith);
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &sat_applied, &sat_ty, "denote_closure_typed: direct combinator call");

                if args.len() == arity {
                    return Some(if returns_clo { Denoted::Clo(sat_applied) } else { Denoted::Int(sat_applied) });
                }

                if !returns_clo {
                    return None; // over-application of a plain Int result: genuinely out of scope
                }
                let extra_args = &args[arity..];
                let sat_applied = Anchored::new(&combinators.cp.arith, sat_applied);
                let mut extra_arg_exprs = Vec::with_capacity(extra_args.len());
                for &a in extra_args {
                    let e = denote_closure_typed(store, a, self_call, param_types, combinators, params)?.int()?;
                    extra_arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                }
                let apply_fn = combinators.cp.apply_ref(extra_args.len());
                let sat_applied = sat_applied.at(&combinators.cp.arith);
                let extra_arg_exprs: Vec<Expr> = extra_arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)).collect();
                let applied = apply_n(apply_fn, std::iter::once(sat_applied).chain(extra_arg_exprs));
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_closure_typed: over-application dispatch");
                return Some(Denoted::Int(applied));
            }
            _ => return None,
        }
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
            let da = denote_closure_typed(store, *a, self_call, param_types, combinators, params)?.int()?;
            let da = Anchored::new(&combinators.cp.arith, da);
            let db = denote_closure_typed(store, *b, self_call, param_types, combinators, params)?.int()?;
            let op_ref = combinators.cp.arith.op_ref(*op);
            let da = da.at(&combinators.cp.arith);
            let applied = kernel::app2(op_ref, da, db);
            let int_ty = combinators.cp.arith.int_ty();
            debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_closure_typed: Prim");
            Some(Denoted::Int(applied))
        }
        // Mirrors `denote_closure`'s identical three-way match: both
        // branches `Int` via `ite_ref`, both `Clo` via `ite_clo_ref`
        // (e.g. a self-call argument `f(n-1, if c then g else h)`,
        // choosing which `Clo`-typed value to thread onward), a mismatch
        // rejected.
        Term::If(c, t, e) => {
            let dc = denote_closure_typed(store, *c, self_call, param_types, combinators, params)?.int()?;
            let dc = Anchored::new(&combinators.cp.arith, dc);
            let dt = denote_closure_typed(store, *t, self_call, param_types, combinators, params)?;
            let dt_is_clo = matches!(dt, Denoted::Clo(_));
            let dt = Anchored::new(&combinators.cp.arith, match dt {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            });
            let de = denote_closure_typed(store, *e, self_call, param_types, combinators, params)?;
            let de_is_clo = matches!(de, Denoted::Clo(_));
            // Anchored before branching -- same staleness reasoning as
            // `denote_closure`'s own identical match.
            let de = Anchored::new(&combinators.cp.arith, match de {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            });
            match (dt_is_clo, de_is_clo) {
                (false, false) => {
                    let ite = combinators.cp.arith.ite_ref();
                    let dc = dc.at(&combinators.cp.arith);
                    let dt = dt.at(&combinators.cp.arith);
                    let de = de.at(&combinators.cp.arith);
                    let applied = kernel::app3(ite, dc, dt, de);
                    let int_ty = combinators.cp.arith.int_ty();
                    debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_closure_typed: If (Int branches)");
                    Some(Denoted::Int(applied))
                }
                (true, true) => {
                    // See `denote_with_placeholders`'s identical case for
                    // why `return_type_of` (not `Denoted::Clo` itself) is
                    // the source of the shared arity here.
                    let t_arity = return_type_of(store, *t, self_call.arity, Some(self_call.idx), param_types).flatten()?;
                    let e_arity = return_type_of(store, *e, self_call.arity, Some(self_call.idx), param_types).flatten()?;
                    if t_arity != e_arity {
                        return None;
                    }
                    let ite_clo = combinators.cp.ite_clo_ref(t_arity);
                    let dc = dc.at(&combinators.cp.arith);
                    let dt = dt.at(&combinators.cp.arith);
                    let de = de.at(&combinators.cp.arith);
                    let applied = kernel::app3(ite_clo, dc, dt, de);
                    let clo_ty = combinators.cp.clo_ty(t_arity);
                    debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &clo_ty, "denote_closure_typed: If (Clo branches)");
                    Some(Denoted::Clo(applied))
                }
                _ => None,
            }
        }
        // A freshly-created closure *value*, not (yet) called -- e.g.
        // threaded onward as the next iteration's own closure-typed
        // parameter, `f(n-1, \y. acc+y)`. Mirrors `denote_closure`'s own
        // value-leaf `Term::Abs | Term::Rec` case exactly.
        Term::Abs(_) => {
            let (arity, body, is_rec) = compile::peel(store, h)?;
            if arity == 0 {
                return None;
            }
            let captures = compile::free_vars(store, body, arity, is_rec);
            let sym = combinators.register(h, &captures, param_types)?;
            if captures.is_empty() {
                return Some(Denoted::Clo(sym));
            }
            let sym = Anchored::new(&combinators.cp.arith, sym);
            let env = build_env_expr(combinators, &captures, params, param_types)?;
            let env_expr = Anchored::new(&combinators.cp.arith, env);
            let sym = sym.at(&combinators.cp.arith);
            let env_expr = env_expr.at(&combinators.cp.arith);
            let applied = kernel::app(sym, env_expr);
            let clo_ty = combinators.cp.clo_ty(arity);
            debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &clo_ty, "denote_closure_typed: capturing closure value");
            Some(Denoted::Clo(applied))
        }
        Term::Rec(_) | Term::App(..) => None,
    }
}

/// A structural pre-pass over one self-call argument *or* one leaf's own
/// expression, mirroring exactly which shapes `denote_closure_typed`/
/// `denote_with_placeholders` will recognize when they later denote this
/// same term for real, but never resolving an actual `Var` value (unlike
/// either of those, no `params` needed) -- purely to force every lazy
/// postulate a nested closure creation/call site will need
/// (`ClosureCombinators::register`/`call_ref`/`pap_ref`, and transitively
/// `ClosurePostulates::mk_env_ref`/`env_ty` for a capturing one) to get
/// pushed *now*, before any temporary `params_and_close_typed` scope gets
/// the chance to trigger one itself and go stale -- see `build_universal`'s
/// own call sites for the full rationale (the same class of bug
/// `apply_ref`'s own upfront pre-push already fixed). Returns `None` for
/// exactly the shapes the real denotation would itself reject, so a
/// priming failure here means the real call would have failed anyway --
/// `build_universal` propagates it with `?`, failing fast before any of
/// the expensive `Ev`/leaf/theorem construction below.
fn prime_closure_postulates(
    store: &TermStore,
    h: Hash,
    self_call: SelfCall,
    param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
) -> Option<()> {
    // Mirrors `find_self_calls`'s own precedence: a self-call occurrence
    // (never appearing inside a self-call argument itself, per
    // `find_self_calls`'s own invariant, so this only ever actually fires
    // when priming a *leaf's own* expression) is a stopping point, not
    // walked into -- its own arguments are primed separately, by
    // `build_universal`'s dedicated pass over `leaf.calls`.
    if compile::match_self_call(store, h, self_call.arity, Some(self_call.idx)).is_some() {
        return Some(());
    }
    if matches!(store.resolve(h), Term::App(..)) {
        let (root, args) = compile::unwind_app_spine(store, h);
        match store.resolve(root) {
            Term::Var(i) => {
                let k = (*param_types.get(*i as usize)?)?;
                if args.len() != k {
                    return None;
                }
                for &a in &args {
                    prime_closure_postulates(store, a, self_call, param_types, combinators)?;
                }
                Some(())
            }
            Term::Abs(_) | Term::Rec(_) => {
                let callee_param_types = param_types_for(store, root)?;
                let arity = callee_param_types.len();
                if args.len() < arity {
                    combinators.pap_ref(root, args.len(), param_types)?;
                    // `pap_ref` itself only primes the pap combinator's own
                    // postulate, not the transitive `mk_env_ref` a
                    // capturing root's own `build_env_expr` call will need
                    // -- that has to be primed here too, the same way the
                    // direct-call branch below primes it, or its first push
                    // can still happen from inside a temporary
                    // `params_and_close_typed` scope and go stale.
                    let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
                    let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
                    if !root_captures.is_empty() {
                        let sig = capture_sig(&root_captures, param_types)?;
                        combinators.cp.mk_env_ref(&sig);
                    }
                } else {
                    // `args.len() >= arity`: primes `call_ref` for root's
                    // own saturated call, shared between an exact match
                    // and an over-application's own leading portion; an
                    // over-application also needs `apply_ref` primed for
                    // its own extra-argument count -- whether the
                    // saturated call's result is actually `Clo`-typed
                    // (required for the real denotation to accept this at
                    // all -- see `combinator_return_type`) isn't checked
                    // here, deliberately: priming just needs to cover
                    // every postulate the real pass *might* touch, and an
                    // unneeded prime for a term the real pass later
                    // rejects anyway is harmless, not unsound.
                    let (c_arity, c_body, c_is_rec) = compile::peel(store, root)?;
                    let captures = compile::free_vars(store, c_body, c_arity, c_is_rec);
                    combinators.call_ref(root, &captures, param_types)?;
                    if !captures.is_empty() {
                        let sig = capture_sig(&captures, param_types)?;
                        combinators.cp.mk_env_ref(&sig);
                    }
                    if args.len() > arity {
                        combinators.cp.apply_ref(args.len() - arity);
                    }
                }
                for &a in &args {
                    prime_closure_postulates(store, a, self_call, param_types, combinators)?;
                }
                Some(())
            }
            _ => None,
        }
    } else {
        match store.resolve(h) {
            Term::Var(_) | Term::Lit(_) => Some(()),
            Term::Prim(_, a, b) => {
                prime_closure_postulates(store, *a, self_call, param_types, combinators)?;
                prime_closure_postulates(store, *b, self_call, param_types, combinators)
            }
            Term::If(c, t, e) => {
                prime_closure_postulates(store, *c, self_call, param_types, combinators)?;
                prime_closure_postulates(store, *t, self_call, param_types, combinators)?;
                prime_closure_postulates(store, *e, self_call, param_types, combinators)
            }
            Term::Abs(_) => {
                let (arity, body, is_rec) = compile::peel(store, h)?;
                if arity == 0 {
                    return None;
                }
                let captures = compile::free_vars(store, body, arity, is_rec);
                combinators.register(h, &captures, param_types)?;
                if !captures.is_empty() {
                    let sig = capture_sig(&captures, param_types)?;
                    combinators.cp.mk_env_ref(&sig);
                }
                Some(())
            }
            Term::Rec(_) | Term::App(..) => None,
        }
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

/// Like [`params_and_close`], but for `build_universal`'s own closure-aware
/// pipeline: pushes one fresh postulate per entry of `param_types`, typed
/// `Clo_k` or `Int` to match (resolved fresh immediately before each
/// individual push and used right away, so even though `clo_ty(k)` may
/// itself lazily push a postulate on a new arity's first use, unlike
/// `Ev`'s own type below, no staleness ordering trick is needed here --
/// see `build_universal`'s own upfront `clo_ty` priming loop, which
/// ensures every arity `param_types` mentions is already primed well
/// before this ever runs, so in practice this never observes a first use
/// anyway), so `build`'s own params may be mixed-typed.
fn params_and_close_typed(
    arith: &mut ClosureCombinators<'_>,
    param_types: &[Option<usize>],
    close: fn(usize, &[Expr], Expr) -> Expr,
    build: impl FnOnce(&mut ClosureCombinators<'_>, &Params) -> Option<Expr>,
) -> Option<Expr> {
    let base_len = arith.p.ctx.len();
    let mut positions = Vec::with_capacity(param_types.len());
    for pt in param_types {
        let ty = match pt {
            Some(k) => arith.clo_ty(*k),
            None => arith.int_ty(),
        };
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
struct UniversalScaffold<'a> {
    combinators: ClosureCombinators<'a>,
    arity: usize,
    /// `param_types[i]` is `Some(k)` for a `Var(i)` parameter that's a
    /// `Clo`, always called with `k` arguments (the same convention
    /// `denote_closure`'s own `param_types` uses -- see its docs), `None`
    /// for a plain `Int` parameter. Never itself involving a captured
    /// free variable or a literal-lambda call (see `build_universal`'s own
    /// docs for the scope this narrows to) -- only ever consulted to
    /// decide whether `instance_from_scaffold` can even attempt a concrete
    /// instance (it can't, for any `Some(_)` entry -- see its own docs).
    param_types: Vec<Option<usize>>,
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

fn build_universal(store: &TermStore, h: Hash) -> Option<UniversalScaffold<'_>> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    if !is_rec || arity == 0 {
        return None;
    }
    let self_idx = arity as u32;
    let self_call = SelfCall { arity, idx: self_idx };

    // `Var(i)` for `i < arity` that's always called, elsewhere in `body`,
    // with a fixed number of arguments (through a parameter, never a
    // literal lambda or a captured free variable -- `self_idx` sits just
    // outside `0..arity`, so a self-call's own callee position never gets
    // misclassified as one of these) is treated as `Clo`-typed throughout
    // this function; everything else stays `Int` -- see the module docs
    // for the fragment this covers and what's still out of scope (closure
    // *creation* anywhere in the body, a captured free variable, an `If`
    // between two closures).
    let found = compile::infer_closure_arities(store, body, arity, Some(self_idx))?;
    let param_types: Vec<Option<usize>> = (0..arity as u32).map(|i| found.get(&i).copied()).collect();

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
    // Always resolves fresh via the caller-supplied `params`, same
    // convention as `ev_of`. Stays purely arithmetic (`classify_tree`
    // already requires a direct comparison here, closures or not).
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
    // `prove_tail_recursive_call`'s convention exactly) -- closure-aware
    // via `denote_closure_typed` (a loop-carried `Clo`-typed argument, or a
    // plain `Int` one possibly computed by calling one), each checked
    // against `param_types[i]`, the *target* slot's own type.
    let new_params_for = |arith: &mut ClosureCombinators<'_>, call_args: &[Hash], params: &[usize]| -> Option<Vec<Expr>> {
        (0..arity)
            .map(|i| {
                let d = denote_closure_typed(store, call_args[arity - 1 - i], self_call, &param_types, arith, params)?;
                match param_types[i] {
                    Some(_) => d.clo(),
                    None => d.int(),
                }
            })
            .collect()
    };

    // Ev : T_0 -> .. -> T_{arity-1} -> Int -> Sort(0) (non-dependent chain:
    // composes correctly via `arrow`'s own shifting regardless of build
    // order -- see `ArithPostulates::new`'s `ite_ty` for the same
    // pattern), each `T_i` `Clo` or `Int` per `param_types[i]`. `v`
    // (innermost -- processed first, below) is pushed before `param_types`
    // in *reverse*, matching `ev_of`/`apply_n`'s own left-to-right
    // application order (`params[0]` applied first, ending up outermost;
    // `v` applied last, ending up innermost).
    let ev_ty = {
        let mut ty = kernel::arrow(arith.int_ty(), kernel::sort(0)); // v : Int
        for pt in param_types.iter().rev() {
            let dom = match pt {
                Some(k) => arith.clo_ty(*k),
                None => arith.int_ty(),
            };
            ty = kernel::arrow(dom, ty);
        }
        ty
    };
    let ev_pos = arith.p.push(ev_ty);
    let ev_of = |arith: &ArithPostulates, params: &[Expr], v: Expr| -> Expr { ev_of(arith, ev_pos, params, v) };

    // Pre-push every `apply_k` arity a closure-typed parameter's own call
    // sites will need, and every `clo_ty(k)`/`ite_clo_ref(k)` (see its own
    // docs -- `clo_ty` eagerly primes both at once) that same parameter's
    // own arity `k` will need, *before* any of the temporary, later-rolled-
    // back `params_and_close_typed` scopes below gets a chance to trigger
    // either's lazy push itself. This memoization
    // (`ClosurePostulates::apply_pos`/`clo_pos`/`ite_clo_pos`) was designed
    // for `prove_closure_expr`'s own usage, where `arith.p.ctx` only ever
    // grows -- there, a postulate's absolute position, once recorded, stays
    // valid forever. Here, `params_and_close_typed` repeatedly
    // pushes-then-truncates the very same scratch space; if a given `k`'s
    // *first* use happened from inside one of those temporary scopes, its
    // pushed postulate would be rolled back while the memoized position
    // stayed recorded, silently going stale (a real bug this caused:
    // `kernel::check` rejected the resulting proof with a lambda-domain
    // mismatch, caught immediately rather than silently accepted -- the
    // memo pointed at whatever postulate happened to occupy that position
    // after later, unrelated growth). Unlike the single, arity-blind `Clo`
    // this fragment used to postulate, there's no longer one universal
    // `clo_ty`/`ite_clo_ref` to prime unconditionally regardless of which
    // arities the term actually uses -- every arity `param_types` mentions
    // is primed here; every *other* arity a `Clo`-typed value could turn
    // out to have (a directly-called combinator's own return type, a
    // partial application's own resulting arity, a freshly-created
    // closure's own peeled arity) is primed transitively below, by
    // `prime_closure_postulates`'s own structural walk through
    // `register`/`call_ref`/`pap_ref` (each of which calls `clo_ty` with
    // the *correct* arity for its own postulate's domain/codomain as part
    // of building it, priming or real construction alike).
    for k in param_types.iter().flatten() {
        arith.apply_ref(*k);
        arith.clo_ty(*k);
    }

    // Same fix, widened: a self-call argument, or a leaf's own top-level
    // expression, may itself *create* a closure and (fully or partially)
    // call it (`denote_closure_typed`'s/`denote_with_placeholders`'s own
    // `Term::Abs | Term::Rec` cases) -- `ClosureCombinators::register`/
    // `call_ref`/`pap_ref`, and transitively `ClosurePostulates::env_ty`/
    // `mk_env_ref` for a capturing one, are *all* lazily memoized the same
    // way `apply_ref` is, so each needs the same upfront priming before
    // `new_params_for`'s/`combines`' first real call (from inside a
    // temporary scope) gets the chance to trigger one itself. Every leaf,
    // both its own expression and every self-call occurrence's own
    // argument list, is scanned once, structurally
    // (`prime_closure_postulates`, which needs no actual parameter
    // *values* -- these registrations depend only on a combinator's
    // `Hash` and a capture *count*, not what the captures currently hold).
    for leaf in &leaves {
        prime_closure_postulates(store, leaf.expr, self_call, &param_types, &mut arith)?;
        for call in &leaf.calls {
            for &a in call {
                prime_closure_postulates(store, a, self_call, &param_types, &mut arith)?;
            }
        }
    }

    // Audited (prompted by the `ite_clo_ref` staleness bug above): every
    // lazily-memoized `ClosurePostulates` field --
    // `apply_pos`/`combinator_value_pos`/`combinator_call_pos`/
    // `env_ty_pos`/`mk_env_pos`/`mk_clo_pos`/`pap_pos`/`ite_clo_pos` -- is
    // now primed above, before any `params_and_close_typed` scope below
    // gets a chance to trigger a first-ever lazy push itself. `literal_pos`
    // is primed even earlier, via the `collect_literals`/`arith.lit(n)`
    // pass this function starts with; `fact_pos`/`ite_fact_pos`
    // (`assume_prim_fact`/`assume_ite_fact`) are exempt on a different
    // footing -- they're only ever touched by `eval_and_prove`, called
    // from `build_ev_witness`/`instance_from_scaffold` *after*
    // `build_universal` has already returned a stable, no-longer-truncated
    // `ctx`, the same non-truncating regime `prove_closure_expr`'s own
    // usage of `apply_ref`/`ite_clo_ref` relies on. A *new* lazily-memoized
    // postulate added to `ClosurePostulates` in the future, reachable from
    // inside `denote_closure_typed`/`denote_with_placeholders`, needs the
    // same treatment (either priming here, if it's `Hash`/signature-keyed
    // like `register`/`call_ref`/`pap_ref`/`mk_env_ref`, or an unconditional
    // prime call like `ite_clo_ref`'s above if it isn't) -- silently
    // missing it doesn't fail loudly the way a compile error would; it
    // waits for a term that happens to hit it from inside a truncating
    // scope. The final `kernel::check` on the assembled theorem
    // (`prove_tail_recursive_universal`'s own trust boundary, unaffected
    // by `debug_assertions`) still catches the resulting ill-typed
    // sub-expression either way, so this never produces an accepted-but-
    // wrong proof -- in a debug build it's a `debug_assert_has_type` panic
    // pinpointing the exact node; in release, `build_universal` just
    // returns `None`, spuriously rejecting a term this fragment should
    // have covered, with no clue *why* beyond re-running under `debug_assertions`.

    // Pushes `v_1:Int .. v_k:Int` then `e_1:Ev(new_params_1,v_1) ..
    // e_k:Ev(new_params_k,v_k)` for a leaf's `calls` (one `(v,e)` pair per
    // self-call occurrence, grouped -- all `v`s then all `e`s -- rather
    // than interleaved; each `e_j`'s type only needs its *own* `v_j`'s
    // position, which stays resolvable via `arith.p.get` regardless of
    // what else has been pushed since, so grouping is no less correct
    // than interleaving and is simpler for every caller below to zip).
    let push_calls = |arith: &mut ClosureCombinators<'_>, pp: &Params, calls: &[Vec<Hash>]| -> Option<(Vec<usize>, Vec<usize>)> {
        let mut v_positions = Vec::with_capacity(calls.len());
        for _ in calls {
            v_positions.push({ let ty = arith.int_ty(); arith.p.push(ty) });
        }
        let mut e_positions = Vec::with_capacity(calls.len());
        for (call, &v_pos) in calls.iter().zip(&v_positions) {
            let np = new_params_for(arith, call, &pp.0)?;
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
    let no_closures = |n: usize| vec![None; n];
    let mut combines = Vec::with_capacity(leaves.len());
    for leaf in &leaves {
        let expr = params_and_close_typed(&mut arith, &param_types, kernel::close_lam, |arith, pp| {
            params_and_close_typed(arith, &no_closures(leaf.calls.len()), kernel::close_lam, |arith, pp2| {
                denote_with_placeholders(store, leaf.expr, self_call, &param_types, arith, &pp.0, &pp2.0, &mut 0)?.int()
            })
        })?;
        combines.push(Anchored::new(&arith, expr));
    }

    // ev_leaf_i : Pi params. Pi (leaf i's path premises). Pi v_1..v_{k_i}
    //             (e_1:Ev(new_params_1,v_1))..(e_{k_i}:..). Ev(params, combine_i(params,vs))
    // -- one constructor per leaf.
    let mut ev_leaf_positions = Vec::with_capacity(leaves.len());
    for (leaf, combine) in leaves.iter().zip(&combines) {
        let ty = params_and_close_typed(&mut arith, &param_types, kernel::close_pi, |arith, pp| {
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
    let motive_ty = params_and_close_typed(&mut arith, &param_types, kernel::close_pi, |arith, pp| {
        let v_pos = { let ty = arith.int_ty(); arith.p.push(ty) };
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
        let ty = params_and_close_typed(&mut arith, &param_types, kernel::close_pi, |arith, pp| {
            let path_positions = push_path(arith, pp, &leaf.path)?;
            let (v_positions, e_positions) = push_calls(arith, pp, &leaf.calls)?;
            // Use phase.
            let params = pp.at(arith);
            let premises = resolve_all(arith, &path_positions);
            let vs = resolve_all(arith, &v_positions);
            let es = resolve_all(arith, &e_positions);
            let mut ih_tys = Vec::with_capacity(leaf.calls.len());
            for ((call, &v_pos), &e_pos) in leaf.calls.iter().zip(&v_positions).zip(&e_positions) {
                let np = new_params_for(arith, call, &pp.0)?;
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
    let concl_ty = params_and_close_typed(&mut arith, &param_types, kernel::close_pi, |arith, pp| {
        let v_pos = { let ty = arith.int_ty(); arith.p.push(ty) };
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
    let const_int_motive_expr = params_and_close_typed(&mut arith, &param_types, kernel::close_lam, |arith, pp| {
        let v_pos = { let ty = arith.int_ty(); arith.p.push(ty) };
        let ev_pv = ev_of(arith, &pp.at(arith), arith.p.get(v_pos));
        arith.p.push(ev_pv); // e : Ev(params, v)
        Some(arith.int_ty())
    })?;
    let const_int_motive = Anchored::new(&arith, const_int_motive_expr);

    let mut loop_leaves = Vec::with_capacity(leaves.len());
    for (leaf, combine) in leaves.iter().zip(&combines) {
        let expr = params_and_close_typed(&mut arith, &param_types, kernel::close_lam, |arith, pp| {
            push_path(arith, pp, &leaf.path)?; // matches leaf_case_ty's premise binders, unused in the body
            push_calls(arith, pp, &leaf.calls)?; // v/e binders, also unused in the body
            let mut ih_positions = Vec::with_capacity(leaf.calls.len());
            for _ in &leaf.calls {
                ih_positions.push({ let ty = arith.int_ty(); arith.p.push(ty) });
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
        let ty = params_and_close_typed(&mut arith, &param_types, kernel::close_pi, |arith, pp| {
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
                let np = new_params_for(arith, call, &pp.0)?;
                recursive_vals.push(loop_val(arith, &np, arith.p.get(v_pos), arith.p.get(e_pos)));
            }
            let rhs = combine_of(arith, combine, &params, &recursive_vals);
            Some(kernel::id(arith.int_ty(), lhs, rhs))
        })?;
        loop_val_leaf_eq_positions.push(arith.p.push(ty));
    }

    // Theorem: Pi params v e. Id(Int, loop_val(params,v,e), v), proved via
    // ev_rec with motive `\params v e. Id(Int, loop_val(params,v,e), v)`.
    let id_motive_expr = params_and_close_typed(&mut arith, &param_types, kernel::close_lam, |arith, pp| {
        let v_pos = { let ty = arith.int_ty(); arith.p.push(ty) };
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
        let expr = params_and_close_typed(&mut arith, &param_types, kernel::close_lam, |arith, pp| {
            let path_positions = push_path(arith, pp, &leaf.path)?;
            let (v_positions, e_positions) = push_calls(arith, pp, &leaf.calls)?;
            let mut ih_positions = Vec::with_capacity(leaf.calls.len());
            for ((call, &v_pos), &e_pos) in leaf.calls.iter().zip(&v_positions).zip(&e_positions) {
                let np = new_params_for(arith, call, &pp.0)?;
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
                let np = new_params_for(arith, call, &pp.0)?;
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

    let theorem_ty = params_and_close_typed(&mut arith, &param_types, kernel::close_pi, |arith, pp| {
        let v_pos = { let ty = arith.int_ty(); arith.p.push(ty) };
        let ev_pv = ev_of(arith, &pp.at(arith), arith.p.get(v_pos));
        let e_pos = arith.p.push(ev_pv);
        // Use phase.
        let params = pp.at(arith);
        let v = arith.p.get(v_pos);
        let e = arith.p.get(e_pos);
        Some(kernel::id(arith.int_ty(), loop_val(arith, &params, v.clone(), e), v))
    })?;

    let theorem_proof = params_and_close_typed(&mut arith, &param_types, kernel::close_lam, |arith, pp| {
        let v_pos = { let ty = arith.int_ty(); arith.p.push(ty) };
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
/// recursion or called via `apply_k`, is covered; so is a closure
/// genuinely created and (fully or partially) called anywhere in the body
/// -- a self-call argument (`f(n-1, (\y. acc+y)(n))`) or a leaf's own
/// top-level expression (`(\y. n+y)(5) + f(n-1)`) alike (see module
/// docs). A leaf may itself contain a further nested `If`, purely
/// arithmetic or choosing between two `Clo`-typed values.
pub fn prove_tail_recursive_universal(store: &TermStore, h: Hash) -> Option<UniversalTailProof> {
    let scaffold = build_universal(store, h)?;
    let theorem_ty = scaffold.theorem_ty.at(&scaffold.combinators);
    let theorem_proof = scaffold.theorem_proof.at(&scaffold.combinators);
    Some(UniversalTailProof {
        ctx: scaffold.combinators.cp.arith.p.ctx,
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
        // Mirrors the `Prim` case just above, via `assume_ite_fact`
        // instead of `assume_prim_fact`: `denote`/`ite_ref` embeds an `If`
        // as fully opaque (both branches always denoted, never
        // short-circuited), so a concrete witness needs the concrete
        // evaluation of *all three* subterms -- `t` and `e` alike, even
        // though only one is the branch `eval_concrete` actually takes --
        // to discharge `app3(ite_ref, dc, dt, de) = lit_ref(result)`.
        Term::If(c, t, e) => {
            let (c, t, e) = (*c, *t, *e);
            let (xc, dc, pc) = eval_and_prove(store, c, arith, params, concrete, param_facts)?;
            let dc = Anchored::new(arith, dc);
            let pc = Anchored::new(arith, pc);
            let (xt, dt, pt) = eval_and_prove(store, t, arith, params, concrete, param_facts)?;
            let dt = Anchored::new(arith, dt);
            let pt = Anchored::new(arith, pt);
            let (xe, de, pe) = eval_and_prove(store, e, arith, params, concrete, param_facts)?;
            let de = Anchored::new(arith, de);
            let pe = Anchored::new(arith, pe);
            let fact = arith.assume_ite_fact(xc, xt, xe);
            let result = if xc != 0 { xt } else { xe };

            let (dc, pc, dt, pt, de, pe) = (dc.at(arith), pc.at(arith), dt.at(arith), pt.at(arith), de.at(arith), pe.at(arith));
            let int_ty = arith.int_ty();
            let f = arith.ite_ref();
            let cong = kernel::cong_n(
                &int_ty,
                &int_ty,
                &f,
                &[dc.clone(), dt.clone(), de.clone()],
                &[arith.lit_ref(xc), arith.lit_ref(xt), arith.lit_ref(xe)],
                vec![pc, pt, pe],
            );
            let lhs = kernel::app3(f.clone(), dc, dt, de);
            let mid = kernel::app3(f, arith.lit_ref(xc), arith.lit_ref(xt), arith.lit_ref(xe));
            let rhs = arith.lit_ref(result);
            let proof = kernel::trans_proof(&int_ty, &lhs, &mid, &rhs, cong, fact);
            debug_assert_has_type(&arith.p.ctx, &proof, &kernel::id(int_ty, lhs.clone(), rhs), "eval_and_prove: If proof");
            Some((result, lhs, proof))
        }
        Term::Abs(_) | Term::App(..) | Term::Rec(_) => None,
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
        ctx: scaffold.combinators.cp.arith.p.ctx.clone(),
        arity: scaffold.arity,
        theorem_ty: scaffold.theorem_ty.at(&scaffold.combinators),
        theorem_proof: scaffold.theorem_proof.at(&scaffold.combinators),
    };
    let instances = args_list
        .iter()
        .map(|args| instance_from_scaffold(store, scaffold.clone(), args))
        .collect();
    Some((theorem, instances))
}

fn instance_from_scaffold(store: &TermStore, mut scaffold: UniversalScaffold<'_>, args: &[i64]) -> Option<UniversalInstanceProof> {
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

    // Fresh past all the growth `build_ev_witness` just did.
    let theorem_proof = scaffold.theorem_proof.at(&scaffold.combinators);
    let params: Vec<Expr> = concrete.iter().map(|&c| scaffold.combinators.lit_ref(c)).collect();
    let applied = apply_n(theorem_proof, params.into_iter().chain([v, e]));
    let ty = kernel::infer(&scaffold.combinators.cp.arith.p.ctx, &applied).ok()?;
    let (lhs, rhs) = match kernel::whnf(&ty) {
        Expr::Id(_, lhs, rhs) => (Rc::unwrap_or_clone(lhs), Rc::unwrap_or_clone(rhs)),
        _ => return None,
    };

    Some(UniversalInstanceProof {
        int_ty: scaffold.combinators.int_ty(),
        ctx: scaffold.combinators.cp.arith.p.ctx,
        arity: scaffold.arity,
        lhs,
        rhs,
        proof: applied,
    })
}

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
// A closure value is postulated opaque (`Clo : Sort(0)`, the same
// "postulated type" pattern `Int` itself uses), and applying one *through
// a parameter* (`call_indirect`) goes through `apply_k : Clo -> Int^k ->
// Int`, postulated once per distinct arity `k` a closure is actually
// called with that way (mirroring `compile.rs`'s own `(type $tyK ...)`
// declarations, one per arity actually used at a `call_indirect` site) --
// this part is unaffected by whether the underlying closure happens to
// capture anything, the same way `compile.rs`'s own `call_indirect`
// dispatch doesn't need to know either.
//
// A combinator's own *body* is never unfolded or denoted here -- it's
// referenced only by postulated symbols. For a *non-capturing* combinator
// this is one `Clo`-typed constant (`combinator_value`, for `h` used as a
// bare value) and one `call_h : T_0 -> .. -> T_{k-1} -> Int` (for a direct
// call), each memoized by hash: faithful on both readings, since a
// non-capturing closure really is the same value everywhere it's
// referenced, and calling it really doesn't need anything beyond its own
// definition. For a *capturing* combinator, one fixed value per
// combinator would be dishonest -- `compile.rs` builds a fresh
// environment at every creation site, so the same combinator denotes
// differently depending on *where* it's referenced -- so instead:
// `mk_clo_h : Env -> Clo` (a function of the environment, not a bare
// constant) and `call_h : Env -> T_0 -> .. -> T_{k-1} -> Int` (the
// environment prepended, mirroring `compile.rs`'s own calling convention
// of `$env` as every combinator's first Wasm parameter), where `Env :
// Sort(0)` is postulated once *per capture signature* (which of its
// slots are `Clo`-typed, which are `Int` -- `capture_sig`; shared across
// every combinator whose captures happen to match that exact signature,
// the same way `apply_k` is shared by arity, not memoized per combinator)
// with constructor `mk_env : T_0 -> .. -> T_{n-1} -> Env`. `build_env_expr`
// builds the actual `mk_env(v_1,...,v_n)` argument fresh at each
// creation site, from whatever the captured values currently are in the
// *calling* function's own frame -- exactly mirroring `compile.rs`'s own
// `push_closure_env` at the proof level. Either way, `apply_k`/`call_h`
// applied to its arguments faithfully represents "call this closure" on
// *both* readings, identically, symbol for symbol, the same way
// `denote`'s postulated `Int` operators represent an arithmetic primitive
// without either reading being numerically verified. The proof is
// `refl`, same as `prove_pure_expr`'s straight-line argument: nothing
// here evaluates anything concrete, so no `assume_prim_fact`-style
// grounding is needed.
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
// `compile_var_read`'s own recursive case, when compiling a function that
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
// Now covers a *capturing* root too, mirroring `compile.rs`'s own
// `push_pap_env`: when `h`'s own body captures anything, `pap_ref`'s
// postulated type takes an extra leading `Env` parameter (the same
// environment-first convention `call_ref` already uses for a direct call),
// and every call site builds that environment via `build_env_expr` and
// prepends it to the wrapper's own supplied arguments -- composing the
// wrapper's own environment with a copy of the root's, exactly the way
// `push_pap_env` composes them at the compiled-code level. Over-application
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
// `is_rec`, and `compile.rs`'s own `register_partial_app`/`emit_pap_wrapper`
// never special-cased it either (a PAP wrapper only ever forwards a static
// call to its root, indifferent to whether that root's own codegen happens
// to loop) -- `pap_ref`'s own extra `is_rec` check was the only thing left
// standing in the way.

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
fn param_types_for(store: &TermStore, h: Hash) -> Option<Vec<Option<usize>>> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    let self_idx = is_rec.then_some(arity as u32);
    let found = compile::infer_closure_arities(store, body, arity, self_idx)?;
    Some((0..arity as u32).map(|i| found.get(&i).copied()).collect())
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
/// result -- always denotes `Int` (the same `apply_k : Clo -> Int -> ..
/// -> Int` convention `denote_closure`'s own `Term::Var(i)` case already
/// relies on), so this only ever needs `h`'s *own* declared parameters'
/// types (`param_types_for`), never a capture's.
fn combinator_return_type(store: &TermStore, h: Hash) -> Option<Option<usize>> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    let self_idx = is_rec.then_some(arity as u32);
    let param_types = param_types_for(store, h)?;
    return_type_of(store, body, arity, self_idx, &param_types)
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
fn return_type_of(store: &TermStore, h: Hash, arity: usize, self_idx: Option<u32>, param_types: &[Option<usize>]) -> Option<Option<usize>> {
    if compile::match_self_call(store, h, arity, self_idx).is_some() {
        return Some(None); // a self-call's own result is always Int
    }
    if matches!(store.resolve(h), Term::App(..)) {
        let (root, args) = compile::unwind_app_spine(store, h);
        return match store.resolve(root) {
            // Calling a parameter, a capture, or (recursively) another
            // directly-called combinator's own result: always Int, the
            // uniform `apply_k`/over-application-dispatch convention.
            Term::Var(_) => Some(None),
            Term::Abs(_) | Term::Rec(_) => {
                let callee_param_types = param_types_for(store, root)?;
                let callee_arity = callee_param_types.len();
                match args.len().cmp(&callee_arity) {
                    std::cmp::Ordering::Equal => combinator_return_type(store, root),
                    // a partial-application value is always Clo, of the
                    // *remaining* arity (the wrapper still expects
                    // `callee_arity - args.len()` more arguments).
                    std::cmp::Ordering::Less => Some(Some(callee_arity - args.len())),
                    std::cmp::Ordering::Greater => Some(None), // over-application's own dispatch is always Int
                }
            }
            _ => None,
        };
    }
    match store.resolve(h) {
        // A bare parameter, read as a value (not called) -- its own
        // declared type; out of range (a bare captured free variable, or
        // this combinator's own self-reference as a plain value, still
        // unsupported) is undetermined, not an error.
        Term::Var(i) => {
            let i = *i as usize;
            if i < arity { Some(*param_types.get(i)?) } else { None }
        }
        Term::Lit(_) | Term::Prim(..) => Some(None),
        Term::If(_, t, e) => {
            let dt = return_type_of(store, *t, arity, self_idx, param_types)?;
            let de = return_type_of(store, *e, arity, self_idx, param_types)?;
            (dt == de).then_some(dt)
        }
        // A fresh closure value, of its own peeled arity.
        Term::Abs(_) | Term::Rec(_) => {
            let (own_arity, _, _) = compile::peel(store, h)?;
            Some(Some(own_arity))
        }
        Term::App(..) => unreachable!("handled above"),
    }
}

/// Extends `ArithPostulates` with postulated closure-value support -- see
/// the section docs above.
#[derive(Clone)]
struct ClosurePostulates {
    arith: ArithPostulates,
    clo_pos: HashMap<usize, usize>,
    apply_pos: HashMap<usize, usize>,
    combinator_value_pos: HashMap<Hash, usize>,
    combinator_call_pos: HashMap<Hash, usize>,
    env_ty_pos: HashMap<Vec<Option<usize>>, usize>,
    mk_env_pos: HashMap<Vec<Option<usize>>, usize>,
    mk_clo_pos: HashMap<Hash, usize>,
    pap_pos: HashMap<(Hash, usize), usize>,
    ite_clo_pos: HashMap<usize, usize>,
}

/// Lets code holding a `&(mut) ClosurePostulates` -- `build_universal`'s own
/// closure-aware pipeline, primarily -- call every `ArithPostulates` method
/// (`int_ty`, `lit_ref`, `p.push`, ...) directly, without a manual `.arith`
/// hop at each use. The one place this bites: *moving* a field out of the
/// inner `ArithPostulates` (e.g. `UniversalTailProof`'s own `ctx:
/// scaffold.combinators.cp.arith.p.ctx`) can't go through a `Deref` (it only
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
    fn new() -> Self {
        let arith = ArithPostulates::new();
        ClosurePostulates {
            arith,
            clo_pos: HashMap::new(),
            apply_pos: HashMap::new(),
            combinator_value_pos: HashMap::new(),
            combinator_call_pos: HashMap::new(),
            env_ty_pos: HashMap::new(),
            mk_env_pos: HashMap::new(),
            mk_clo_pos: HashMap::new(),
            pap_pos: HashMap::new(),
            ite_clo_pos: HashMap::new(),
        }
    }

    /// `Clo_arity : Sort(0)`, one postulate per distinct arity, mirroring
    /// how `Env_sig` is already postulated per capture signature -- the
    /// kernel-level fix for the "arity-blind `Clo`" gap `TYPES.md` (section
    /// 7) describes: two closures of different real arity now get
    /// genuinely distinct, definitionally-unequal kernel types instead of
    /// sharing one opaque `Clo`, so `kernel::check`'s own definitional-
    /// equality checking rejects an arity mismatch (a call, a capture, an
    /// `If` between two differently-sized closures) on its own, without any
    /// new Rust-level bookkeeping to detect it -- every call site below
    /// just has to ask for the *correct* arity, already available locally
    /// (a parameter's own declared arity, a literal lambda's own peeled
    /// arity, or `combinator_return_type`'s own classification), the same
    /// discipline `Env_sig` already required for capture signatures.
    /// Also eagerly primes `ite_clo_ref(arity)`'s own postulate at the same
    /// time (see its own docs for why bundling here, rather than a
    /// separate inference pass, is enough to prime it safely).
    fn clo_ty(&mut self, arity: usize) -> Expr {
        if let Some(&pos) = self.clo_pos.get(&arity) {
            return self.arith.p.get(pos);
        }
        let pos = self.arith.p.push(kernel::sort(0));
        self.clo_pos.insert(arity, pos);
        let clo_ty = self.arith.p.get(pos);
        let ite_ty = kernel::arrow(self.arith.int_ty(), kernel::arrow(clo_ty.clone(), kernel::arrow(clo_ty.clone(), clo_ty)));
        let ite_pos = self.arith.p.push(ite_ty);
        self.ite_clo_pos.insert(arity, ite_pos);
        // Re-resolve fresh, rather than returning the `clo_ty` value
        // captured above: the `ite_clo` push just above grew `p.ctx` by
        // one more since that value was itself resolved, which would
        // otherwise leave it stale by exactly one at the depth this
        // function actually returns to its caller -- the same staleness
        // class `Anchored`'s own docs describe, here escaping this
        // function's own boundary (a caller holding the returned `Expr`
        // unanchored across any further push of its own) rather than a
        // caller's own already-anchored value.
        self.arith.p.get(pos)
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
        // `clo_ty(k)` first, before either `int_ty()` read below: it may
        // lazily push a fresh `Clo_k`/`ite_clo_k` pair (the first time
        // this particular arity is seen), which would silently invalidate
        // an `int_ty()` reference already folded into `ty` if it ran
        // after instead -- the same staleness class `Anchored`'s own docs
        // describe, just inside a single function's own type
        // construction. `int_ty()` itself never pushes, so once `clo_ty`
        // is out of the way, nothing below can invalidate anything else.
        let dom = self.clo_ty(k);
        let mut ty = self.arith.int_ty();
        for _ in 0..k {
            ty = kernel::arrow(self.arith.int_ty(), ty);
        }
        let ty = kernel::arrow(dom, ty);
        let pos = self.arith.p.push(ty);
        self.apply_pos.insert(k, pos);
        self.arith.p.get(pos)
    }

    /// `ite_clo_arity : Int -> Clo_arity -> Clo_arity -> Clo_arity`,
    /// postulated once per distinct `arity` (lazily, unlike
    /// `ArithPostulates::ite_ref`'s eager one -- a term never choosing
    /// between two closures of that particular arity shouldn't pay for
    /// this postulate) -- the `Clo_arity`-valued counterpart to `ite_ref`,
    /// needed for an `If` that chooses between two same-arity closures
    /// rather than two `Int`s (e.g. `if c then (\y. x+y) else (\y. x-y)`).
    /// The condition itself stays `Int` either way -- only the two
    /// branches (and the result) differ. Always primed as a side effect of
    /// `clo_ty(arity)`'s own first call (see its docs) -- this just looks
    /// up the now-guaranteed-present position.
    fn ite_clo_ref(&mut self, arity: usize) -> Expr {
        self.clo_ty(arity);
        let pos = self.ite_clo_pos[&arity];
        self.arith.p.get(pos)
    }

    /// A fresh `Clo_arity`-typed constant for combinator `h` (own arity
    /// `arity`), memoized by hash -- for a *non-capturing* combinator used
    /// as a bare value (an argument, a branch result, ...), mirroring
    /// `compile.rs`'s "its value is just its table index" reading. A
    /// *capturing* combinator's own value needs `mk_clo_ref` instead --
    /// see its docs for why one fixed constant isn't an honest model there.
    fn combinator_value(&mut self, h: Hash, arity: usize) -> Expr {
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
    /// happen to match this exact signature, the same way `apply_k` is
    /// shared across every closure called with `k` arguments regardless of
    /// which combinator it turns out to be -- two combinators that both
    /// capture, say, three plain `Int`s still share one `Env` (the common
    /// case, keyed by an all-`None` signature exactly as it used to be
    /// keyed by the count `3` alone); only a genuinely mixed, or
    /// genuinely differently-sized-closure, signature gets its own.
    fn env_ty(&mut self, sig: &[Option<usize>]) -> Expr {
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
    fn mk_env_ref(&mut self, sig: &[Option<usize>]) -> Expr {
        if let Some(&pos) = self.mk_env_pos.get(sig) {
            return self.arith.p.get(pos);
        }
        // Unlike the single, arity-blind `Clo` this fragment used to
        // postulate, `env_ty`/`clo_ty` here can *each* lazily push their
        // own postulate on first use -- possibly several times over, once
        // per distinct arity `sig` mentions -- so no single "resolve the
        // one lazy thing first" ordering trick (like `apply_ref`'s own
        // fix) suffices. Each is anchored immediately after resolving it
        // instead, and only re-resolved (`.at`), fresh, once nothing more
        // is left to push -- the same discipline `denote_closure`'s own
        // composite cases use for a whole built term, one level up.
        let env_ty = self.env_ty(sig);
        let env_ty = Anchored::new(&self.arith, env_ty);
        let doms: Vec<Anchored> = sig
            .iter()
            .map(|slot| {
                let dom = match slot {
                    Some(k) => self.clo_ty(*k),
                    None => self.arith.int_ty(),
                };
                Anchored::new(&self.arith, dom)
            })
            .collect();
        let mut ty = env_ty.at(&self.arith);
        // Fold from the *last* capture outward, so the final iteration
        // (sig[0]) ends up as the outermost/first-applied parameter,
        // matching `apply_n`'s left-to-right application order (the same
        // convention `call_ref`'s own loop documents).
        for dom in doms.iter().rev() {
            ty = kernel::arrow(dom.at(&self.arith), ty);
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
    fn mk_clo_ref(&mut self, h: Hash, sig: &[Option<usize>], arity: usize) -> Expr {
        if let Some(&pos) = self.mk_clo_pos.get(&h) {
            return self.arith.p.get(pos);
        }
        // `env_ty(sig)` and `clo_ty(arity)` may *each* lazily push their
        // own postulate on first use -- same discipline as `mk_env_ref`'s
        // identical fix, just for two pieces instead of `sig.len() + 1`.
        let env_ty = self.env_ty(sig);
        let env_ty = Anchored::new(&self.arith, env_ty);
        let clo_ty = self.clo_ty(arity);
        let ty = kernel::arrow(env_ty.at(&self.arith), clo_ty);
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
struct ClosureCombinators<'a> {
    store: &'a TermStore,
    cp: ClosurePostulates,
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
    fn new(store: &'a TermStore) -> Self {
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
    fn register(&mut self, h: Hash, captures: &[u32], caller_param_types: &[Option<usize>]) -> Option<Expr> {
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
    /// -- unlike `apply_ref`, there's no leading `Clo` argument here),
    /// memoized by hash: `T_0 -> T_1 -> .. -> T_{k-1} -> R` if `h`
    /// doesn't capture anything, or `Env -> T_0 -> .. -> T_{k-1} -> R`
    /// (`n` = `captures.len()`) if it does -- the environment, when
    /// present, is always the *first* parameter, ahead of `h`'s own
    /// call arguments, mirroring `compile.rs`'s own calling convention
    /// (every combinator takes `$env` as its first Wasm parameter,
    /// whether or not its own body reads from it). Each `T_j` (`j` in
    /// application order, i.e. `T_0` is the *first*-applied argument's
    /// type) is `Clo` or `Int` matching `h`'s own `param_types` at that
    /// position -- this is what lets a combinator like `twice`
    /// (`Clo -> Int -> Int`, since its own `f` parameter is itself
    /// closure-typed) be called with a mix of closure and plain-`Int`
    /// arguments, which the uniform `apply_k` can't express. `R` itself
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
    fn call_ref(&mut self, h: Hash, captures: &[u32], caller_param_types: &[Option<usize>]) -> Option<Expr> {
        if let Some(&pos) = self.cp.combinator_call_pos.get(&h) {
            return Some(self.cp.arith.p.get(pos));
        }
        let param_types = param_types_for(self.store, h)?;
        let return_ty = combinator_return_type(self.store, h).unwrap_or(None);
        let sig = capture_sig(captures, caller_param_types)?;
        // Every piece below (`env_ty`, the return type's own `clo_ty`,
        // each parameter's own `clo_ty`) may lazily push its own
        // postulate on first use -- possibly several times over, once per
        // distinct arity involved -- so unlike when only `env_ty` itself
        // could ever push (back when `Clo` was a single, always-eager
        // postulate), no single "resolve the one lazy thing first"
        // ordering trick suffices any more. Each piece is anchored
        // immediately after resolving it instead, and only re-resolved
        // (`.at`), fresh, once nothing more is left to push -- the same
        // discipline `denote_closure`'s own composite cases use for a
        // whole built term, one level up.
        let env_ty = (!sig.is_empty()).then(|| {
            let e = self.cp.env_ty(&sig);
            Anchored::new(&self.cp.arith, e)
        });
        let ret = match return_ty {
            Some(k) => self.cp.clo_ty(k),
            None => self.cp.arith.int_ty(),
        };
        let ret = Anchored::new(&self.cp.arith, ret);
        let doms: Vec<Anchored> = param_types
            .iter()
            .map(|pt| {
                let dom = match pt {
                    Some(k) => self.cp.clo_ty(*k),
                    None => self.cp.arith.int_ty(),
                };
                Anchored::new(&self.cp.arith, dom)
            })
            .collect();
        let mut ty = ret.at(&self.cp.arith);
        // Var(0) is last-applied (innermost -- wrap it first, so the
        // final iteration, Var(arity-1) = first-applied, ends up
        // outermost, matching apply_n's left-to-right application order).
        for dom in &doms {
            ty = kernel::arrow(dom.at(&self.cp.arith), ty);
        }
        if let Some(env_ty) = env_ty {
            ty = kernel::arrow(env_ty.at(&self.cp.arith), ty);
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
    /// If `h` itself captures (`compile.rs`'s own `push_pap_env` composes
    /// the wrapper's own environment with a copy of `h`'s -- see its own
    /// docs), `mk_pap_h_k` takes `h`'s own `Env` first, ahead of the `k`
    /// supplied arguments, mirroring `call_h`'s own environment-first
    /// convention: `Env -> T_0 -> .. -> T_{k-1} -> Clo`. `caller_param_types`
    /// (the *calling* scope's own `param_types`) resolves `h`'s own
    /// captures' `Clo`/`Int` signature, the same way `register`/`call_ref`
    /// do. `env_ty`/`clo_ty` are each individually anchored below, same as
    /// `call_ref`'s own fix for the identical hazard: any of them may
    /// lazily push a fresh postulate on its own first use, which would
    /// silently invalidate an already-resolved sibling `Expr` if held
    /// past that push unshifted.
    ///
    /// `None` for a zero-`k` or over-`k` (`k >= arity`) root -- `h` may
    /// itself be self-recursive (`Term::Rec`, not just `Term::Abs`):
    /// `compile::peel`/`compile::free_vars`/`param_types_for` are all
    /// already generic over that (a call is always postulated opaque
    /// regardless), and `compile.rs`'s own `register_partial_app`/
    /// `emit_pap_wrapper` never special-cased it either -- a static
    /// forwarding call to `root`'s own table entry, indifferent to
    /// whether that entry's *own* codegen happens to loop.
    fn pap_ref(&mut self, h: Hash, k: usize, caller_param_types: &[Option<usize>]) -> Option<Expr> {
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
        // Same discipline as `call_ref`'s identical fix: `env_ty` and
        // every `clo_ty` below may each lazily push their own postulate,
        // so each is anchored immediately and only re-resolved (`.at`)
        // once nothing more is left to push.
        let env_ty = (!sig.is_empty()).then(|| {
            let e = self.cp.env_ty(&sig);
            Anchored::new(&self.cp.arith, e)
        });
        let ret = self.cp.clo_ty(arity - k);
        let ret = Anchored::new(&self.cp.arith, ret);
        let doms: Vec<Anchored> = param_types[arity - k..]
            .iter()
            .map(|pt| {
                let dom = match pt {
                    Some(j) => self.cp.clo_ty(*j),
                    None => self.cp.arith.int_ty(),
                };
                Anchored::new(&self.cp.arith, dom)
            })
            .collect();
        let mut ty = ret.at(&self.cp.arith);
        for dom in &doms {
            ty = kernel::arrow(dom.at(&self.cp.arith), ty);
        }
        if let Some(env_ty) = env_ty {
            ty = kernel::arrow(env_ty.at(&self.cp.arith), ty);
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
fn capture_sig(captures: &[u32], caller_param_types: &[Option<usize>]) -> Option<Vec<Option<usize>>> {
    captures.iter().map(|&rel| caller_param_types.get(rel as usize).copied()).collect()
}

/// Builds `mk_env(v_1,...,v_n)` for a combinator whose relative capture
/// indices are `captures` (`compile::free_vars`), reading each captured
/// value's *current* value out of the *calling* function's own
/// `(params, param_types)` frame -- mirroring `compile.rs`'s
/// `push_closure_env`, but resolving each slot directly against `params`
/// rather than through a `compile_var_read`-style recursive lookup (see
/// `build_env_expr`'s own section docs above for why that recursive case
/// never actually arises here). Each captured index must resolve
/// directly to one of the caller's own parameters (`rel < params.len()`)
/// -- but may be `Clo`-typed or `Int`-typed freely; `capture_sig` picks
/// out which, and `Env`/`mk_env` are keyed by that signature rather than
/// assuming every capture is `Int`.
fn build_env_expr(combinators: &mut ClosureCombinators, captures: &[u32], params: &[usize], param_types: &[Option<usize>]) -> Option<Expr> {
    let sig = capture_sig(captures, param_types)?;
    let mut values = Vec::with_capacity(captures.len());
    for &rel in captures {
        let v = combinators.cp.arith.p.get(*params.get(rel as usize)?);
        values.push(Anchored::new(&combinators.cp.arith, v));
    }
    let mk_env_expr = combinators.cp.mk_env_ref(&sig);
    let mk_env = Anchored::new(&combinators.cp.arith, mk_env_expr);
    let mk_env = mk_env.at(&combinators.cp.arith);
    let values: Vec<Expr> = values.iter().map(|v| v.at(&combinators.cp.arith)).collect();
    Some(apply_n(mk_env, values))
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
            Term::Abs(_) | Term::Rec(_) => matches!(compile::peel(store, root), Some((a, _, _)) if a > 0),
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
        Term::Abs(_) | Term::Rec(_) => true, // a bare value -- opaque, nothing inside it to collect
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
            // A literal lambda -- or a named self-recursive combinator, the
            // same table `Term::Abs` uses (compile.rs's own combinator
            // table doesn't distinguish self-recursive from not; neither
            // does this, since a call is postulated opaque either way --
            // see `param_types_for`/`ClosureCombinators::register`/
            // `call_ref`, all already generic over `is_rec`) -- in function
            // position, applied to exactly its own arity (a direct static
            // call), fewer arguments than its own arity (compile.rs's
            // compile-time-desugared partial application,
            // `register_partial_app`'s wrapper -- `pap_ref` covers a
            // self-recursive root here too, the same opaque-call reasoning),
            // or more (over-application: `root`'s own saturated call is
            // built first, exactly as the direct-call case below does, then
            // whatever it denotes is dispatched on the extra arguments via
            // `apply_ref`, exactly like the `Term::Var(i)` case above --
            // see `combinator_return_type`'s own docs for why this is sound
            // without denoting `root`'s body in the usual sense).
            // Each argument's expected type matches the *callee's own*
            // parameter type at that position (`Clo` or `Int`), which is
            // what lets e.g. `twice(inc, 5)` pass a closure and a plain
            // `Int` to the same call.
            Term::Abs(_) | Term::Rec(_) => {
                let callee_param_types = param_types_for(store, root)?;
                let arity = callee_param_types.len();
                if args.len() < arity {
                    // Compile-time-desugared partial application: build
                    // mk_pap_root_k(a_1,...,a_k), a Clo-typed value -- see
                    // pap_ref's own docs for why the supplied arguments are
                    // denoted normally here rather than resolved through any
                    // Env/build_env_expr-style machinery (unlike root's
                    // *own* environment, when it captures, which does need
                    // build_env_expr, exactly as a direct call to a
                    // capturing root does above).
                    let k = args.len();
                    let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
                    let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
                    let pap_fn = combinators.pap_ref(root, k, param_types)?;
                    let pap_fn = Anchored::new(&combinators.cp.arith, pap_fn);
                    let env_expr = if root_captures.is_empty() {
                        None
                    } else {
                        let e = build_env_expr(combinators, &root_captures, params, param_types)?;
                        Some(Anchored::new(&combinators.cp.arith, e))
                    };
                    let mut arg_exprs = Vec::with_capacity(k);
                    for (j, &a) in args.iter().enumerate() {
                        // args[j] (application order) is Var(arity-1-j) --
                        // see param_types_for's/denote's own convention;
                        // unchanged by only k of arity args being supplied.
                        let d = denote_closure(store, a, combinators, params, param_types)?;
                        let e = match callee_param_types[arity - 1 - j] {
                            Some(_) => d.clo()?,
                            None => d.int()?,
                        };
                        arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                    }
                    let pap_fn = pap_fn.at(&combinators.cp.arith);
                    let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                    if let Some(env_expr) = &env_expr {
                        all_args.push(env_expr.at(&combinators.cp.arith));
                    }
                    all_args.extend(arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)));
                    let applied = apply_n(pap_fn, all_args);
                    // Anchored *before* computing `clo_ty(arity - k)`
                    // below -- see `denote_with_placeholders`'s identical
                    // case for the rationale.
                    let applied = Anchored::new(&combinators.cp.arith, applied);
                    let clo_ty = combinators.cp.clo_ty(arity - k);
                    let applied = applied.at(&combinators.cp.arith);
                    debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &clo_ty, "denote_closure: partial application");
                    return Some(Denoted::Clo(applied));
                }
                // `args.len() >= arity`: build `root`'s own saturated call
                // first -- shared between an exact match and an
                // over-application's own leading portion.
                let sat_args = &args[..arity];
                let (c_arity, c_body, c_is_rec) = compile::peel(store, root)?;
                let captures = compile::free_vars(store, c_body, c_arity, c_is_rec);
                let call_fn = combinators.call_ref(root, &captures, param_types)?;
                let call_fn = Anchored::new(&combinators.cp.arith, call_fn);
                let env_expr = if captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &captures, params, param_types)?;
                    Some(Anchored::new(&combinators.cp.arith, e))
                };
                let mut arg_exprs = Vec::with_capacity(arity);
                for (j, &a) in sat_args.iter().enumerate() {
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
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.at(&combinators.cp.arith));
                }
                all_args.extend(arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)));
                let sat_applied = apply_n(call_fn, all_args);
                // Anchored *before* `combinator_return_type`'s own
                // `clo_ty(k)` lookup below -- see
                // `denote_with_placeholders`'s identical case for the
                // rationale.
                let sat_applied = Anchored::new(&combinators.cp.arith, sat_applied);
                let return_ty = combinator_return_type(store, root).unwrap_or(None);
                let returns_clo = return_ty.is_some();
                let sat_ty = match return_ty {
                    Some(k) => combinators.cp.clo_ty(k),
                    None => combinators.cp.arith.int_ty(),
                };
                let sat_applied = sat_applied.at(&combinators.cp.arith);
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &sat_applied, &sat_ty, "denote_closure: direct combinator call");

                if args.len() == arity {
                    return Some(if returns_clo { Denoted::Clo(sat_applied) } else { Denoted::Int(sat_applied) });
                }

                // Over-application: dispatch the extra arguments on
                // `root`'s own saturated result through `apply_ref`,
                // exactly like calling a closure-typed variable (the
                // `Term::Var(i)` case above), just with the callee
                // freshly computed rather than read from `params`. Only
                // sound when that result genuinely denotes a further
                // `Clo` -- unlike compile.rs (which has no type system to
                // check this at all, relying entirely on jit.rs's sample
                // verification), an unsound premise here would let the
                // kernel "prove" something false, so a plain-`Int`
                // `sat_applied` rejects outright rather than compiling a
                // bad proof.
                if !returns_clo {
                    return None;
                }
                let extra_args = &args[arity..];
                let sat_applied = Anchored::new(&combinators.cp.arith, sat_applied);
                let mut extra_arg_exprs = Vec::with_capacity(extra_args.len());
                for &a in extra_args {
                    let e = denote_closure(store, a, combinators, params, param_types)?.int()?;
                    extra_arg_exprs.push(Anchored::new(&combinators.cp.arith, e));
                }
                let apply_fn = combinators.cp.apply_ref(extra_args.len());
                let sat_applied = sat_applied.at(&combinators.cp.arith);
                let extra_arg_exprs: Vec<Expr> = extra_arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)).collect();
                let applied = apply_n(apply_fn, std::iter::once(sat_applied).chain(extra_arg_exprs));
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_closure: over-application dispatch");
                return Some(Denoted::Int(applied));
            }
            _ => return None,
        }
    }

    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        let dc = denote_closure(store, c, combinators, params, param_types)?.int()?;
        let dc = Anchored::new(&combinators.cp.arith, dc);
        let dt = denote_closure(store, t, combinators, params, param_types)?;
        let dt_is_clo = matches!(dt, Denoted::Clo(_));
        let dt = Anchored::new(&combinators.cp.arith, match dt {
            Denoted::Int(e) | Denoted::Clo(e) => e,
        });
        let de = denote_closure(store, e, combinators, params, param_types)?;
        let de_is_clo = matches!(de, Denoted::Clo(_));
        // Anchored *before* branching on `dt_is_clo`/`de_is_clo`, not just
        // resolved inline in each arm below: `ite_clo_ref` (unlike
        // `ite_ref`, which never pushes) lazily postulates on its first
        // use, which would otherwise silently invalidate an unanchored
        // `dt`/`de` held across that push -- the exact staleness class
        // `Anchored`'s own docs describe (caught immediately by
        // `debug_assert_has_type` on the very first Clo-branch test,
        // before it could reach anything outside this module).
        let de = Anchored::new(&combinators.cp.arith, match de {
            Denoted::Int(e) | Denoted::Clo(e) => e,
        });
        // Both branches Int (the common case) or both Clo (an If choosing
        // between two closures, e.g. `if c then (\y.x+y) else (\y.x-y)`) --
        // a mismatch (one of each) is rejected, same as any other
        // Int/Clo confusion in this fragment.
        return match (dt_is_clo, de_is_clo) {
            (false, false) => {
                let ite = combinators.cp.arith.ite_ref(); // pre-postulated once in ArithPostulates::new -- never pushes
                let dc = dc.at(&combinators.cp.arith);
                let dt = dt.at(&combinators.cp.arith);
                let de = de.at(&combinators.cp.arith);
                let applied = kernel::app3(ite, dc, dt, de);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "denote_closure: If (Int branches)");
                Some(Denoted::Int(applied))
            }
            (true, true) => {
                // See `denote_with_placeholders`'s identical case for why
                // `return_type_of` (not `Denoted::Clo` itself) is the
                // source of the shared arity here; `denote_closure` has no
                // self-call concept of its own (`prove_closure_expr` never
                // sets one up), so `self_idx` is always `None` and `arity`
                // is this whole function's own top-level arity
                // (`param_types.len()`), the same pair `Var(i)`'s own
                // in-range check just below already relies on.
                let top_arity = param_types.len();
                let t_arity = return_type_of(store, t, top_arity, None, param_types).flatten()?;
                let e_arity = return_type_of(store, e, top_arity, None, param_types).flatten()?;
                if t_arity != e_arity {
                    return None;
                }
                let ite_clo = combinators.cp.ite_clo_ref(t_arity);
                let dc = dc.at(&combinators.cp.arith);
                let dt = dt.at(&combinators.cp.arith);
                let de = de.at(&combinators.cp.arith);
                let applied = kernel::app3(ite_clo, dc, dt, de);
                let clo_ty = combinators.cp.clo_ty(t_arity);
                debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &clo_ty, "denote_closure: If (Clo branches)");
                Some(Denoted::Clo(applied))
            }
            _ => None,
        };
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
        // A literal lambda used as a bare value -- or a named self-recursive
        // combinator (`Term::Rec`) used the same way, e.g. `let fact = rec
        // f n = .. in g fact` -- register/build_env_expr are already
        // generic over `is_rec` (see the App-root match above), so this
        // only ever needed widening the pattern, not the logic: whether
        // `h` recurses is never examined, since a call is postulated
        // opaque either way.
        Term::Abs(_) | Term::Rec(_) => {
            let (arity, body, is_rec) = compile::peel(store, h)?;
            if arity == 0 {
                return None;
            }
            let captures = compile::free_vars(store, body, arity, is_rec);
            let sym = combinators.register(h, &captures, param_types)?;
            if captures.is_empty() {
                return Some(Denoted::Clo(sym));
            }
            let sym = Anchored::new(&combinators.cp.arith, sym);
            let env = build_env_expr(combinators, &captures, params, param_types)?;
            let env_expr = Anchored::new(&combinators.cp.arith, env);
            let sym = sym.at(&combinators.cp.arith);
            let env_expr = env_expr.at(&combinators.cp.arith);
            let applied = kernel::app(sym, env_expr);
            let clo_ty = combinators.cp.clo_ty(arity);
            debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &clo_ty, "denote_closure: capturing closure value");
            Some(Denoted::Clo(applied))
        }
        Term::If(..) | Term::App(..) => unreachable!("handled above"),
    }
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
/// returning one is covered, dispatched via `apply_ref` on the extra
/// arguments), an `If` whose branches aren't both `Int` or both `Clo` (or
/// one of each), a whole-function result that isn't `Int`, a captured
/// value (for a capturing combinator) that doesn't resolve directly to
/// one of the calling function's own parameters (freely `Int`- or
/// `Clo`-typed -- see `build_env_expr`'s own docs), or a partial
/// application (fewer arguments than arity) whose root itself captures
/// anything or is itself self-recursive.
pub fn prove_closure_expr(store: &TermStore, h: Hash) -> Option<EquivalenceProof> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    if is_rec {
        return None;
    }

    let found = compile::infer_closure_arities(store, body, arity, None)?;
    let param_types: Vec<Option<usize>> = (0..arity as u32).map(|i| found.get(&i).copied()).collect();

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
    use crate::eval;
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

    /// `rec f n g x = if n <= 0 then x else f(n-1, g, g(x))` -- "iterate a
    /// closure-typed parameter `n` times, starting at `x`", tail-recursive,
    /// threading `g` (a `Clo`-typed parameter, called via `apply_k`
    /// each iteration) through the recursion unchanged -- the fragment
    /// `build_universal`'s own `param_types` extension covers: a
    /// closure-typed *parameter*, never a closure *created* inside the
    /// body. `n`=Var(2), `g`=Var(1), `x`=Var(0) inside the body (innermost
    /// parameter bound first, same convention `gcd`'s own builder above
    /// uses).
    fn iterate(s: &mut TermStore) -> Hash {
        let x = s.var(0);
        let g = s.var(1);
        let n = s.var(2);
        let f = s.var(3);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let gx = s.app(g, x);
        let f_n1_g = s.app2(f, n_minus_1, g);
        let rec_call = s.app(f_n1_g, gx);
        let body = s.if_(cond, x, rec_call);
        let g_binder = s.abs(body);
        let n_binder = s.abs(g_binder);
        let abs = s.abs(n_binder);
        s.rec(abs)
    }

    #[test]
    fn a_closure_typed_loop_carried_parameter_gets_a_universal_proof() {
        let mut s = TermStore::new();
        let it = iterate(&mut s);

        let proof = prove_tail_recursive_universal(&s, it).expect("iterate should get a universal proof");
        assert_eq!(proof.arity, 3);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");
    }

    /// `rec f n acc = if n <= 0 then acc else f(n-1, (\y. acc+y)(n))` --
    /// tail-recursive, each iteration *creates and immediately calls* a
    /// fresh capturing closure (`\y. acc+y`, capturing `acc`) within the
    /// self-call's own argument list -- the exact shape
    /// `compile::tests::self_recursion_creating_a_fresh_capturing_closure_every_iteration_compiles`/
    /// `jit::tests::capturing_closure_loop` already exercise at the
    /// compile/JIT level. `n`=Var(1), `acc`=Var(0), `f`=Var(2) at the
    /// body's own top level -- inside the closure's own body, `acc` is
    /// Var(1) (one more binder, `y`, in the way), matching
    /// `benches/common.rs`'s own builder exactly.
    fn capturing_closure_loop(s: &mut TermStore) -> Hash {
        let y = s.var(0);
        let acc_captured = s.var(1);
        let sum = s.prim(PrimOp::Add, acc_captured, y);
        let closure = s.abs(sum);
        let n_ref = s.var(1);
        let new_acc = s.app(closure, n_ref);
        let n = s.var(1);
        let acc = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let f = s.var(2);
        let f_n1 = s.app(f, n_minus_1);
        let rec_call = s.app(f_n1, new_acc);
        let body = s.if_(cond, acc, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        s.rec(abs)
    }

    #[test]
    fn a_closure_created_and_called_inside_a_self_call_argument_gets_a_universal_proof() {
        let mut s = TermStore::new();
        let h = capturing_closure_loop(&mut s);

        let proof = prove_tail_recursive_universal(&s, h)
            .expect("a self-recursive loop creating a fresh capturing closure each iteration should get a universal proof");
        assert_eq!(proof.arity, 2);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");

        // Instance specialization (the weaker, sample-oriented proof --
        // `kernel_verified` never depended on it, see `jit.rs`'s own docs)
        // still declines here, an honest gap this round didn't close:
        // `eval_and_prove` -- unchanged, deliberately out of scope -- still
        // rejects `App`/`Abs` outright, so a self-call argument that
        // *creates* a closure can't get a concrete witness yet, unlike a
        // closure-typed *parameter* (which `instance_from_scaffold`'s own
        // `param_types`-based guard declines explicitly; this term's
        // `param_types` are all `None`, so that guard never even triggers
        // -- `eval_and_prove` itself is what says no here).
        assert!(prove_tail_recursive_instance(&s, h, &[5, 0]).is_none());

        assert!(compile::try_compile(&s, h).is_some());
    }

    #[test]
    fn a_capturing_partial_application_created_inside_a_self_call_argument_gets_a_universal_proof() {
        // rec f n acc = if n <= 0 then acc else f(n-1, caller(capturing_add(n)))
        // where capturing_add = \x y. x + y + acc (captures f's own second
        // parameter) and caller = \g. g(4) -- same shape as
        // capturing_closure_loop above, but the self-call argument
        // partially applies a *capturing* literal lambda (one argument
        // short) and completes it through caller, rather than creating and
        // immediately calling a fully-applied closure. This is exactly the
        // shape that exposed a real staleness bug: prime_closure_postulates's
        // own partial-application branch primed pap_ref but not the
        // transitive mk_env_ref a capturing root's build_env_expr call also
        // needs, so that lazy push could still happen for the first time
        // from inside a rolled-back params_and_close_typed scope -- caught
        // by compile_fuzz's random-term fuzzing before this dedicated
        // regression test existed.
        let mut s = TermStore::new();
        let x = s.var(1);
        let y = s.var(0);
        let acc_captured = s.var(2); // acc, shifted by capturing_add's own 2 binders
        let xy = s.prim(PrimOp::Add, x, y);
        let xyz = s.prim(PrimOp::Add, xy, acc_captured);
        let inner_ca = s.abs(xyz);
        let capturing_add = s.abs(inner_ca);

        let n_ref = s.var(1);
        let partial = s.app(capturing_add, n_ref); // capturing_add(n) -- one arg short

        let g = s.var(0);
        let four = s.lit(4);
        let call_g = s.app(g, four);
        let caller = s.abs(call_g);

        let new_acc = s.app(caller, partial); // caller(partial) = n + 4 + acc

        let n = s.var(1);
        let acc = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let f = s.var(2);
        let f_n1 = s.app(f, n_minus_1);
        let rec_call = s.app(f_n1, new_acc);
        let body = s.if_(cond, acc, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        let h = s.rec(abs);

        let proof = prove_tail_recursive_universal(&s, h)
            .expect("a self-recursive loop partially applying a fresh capturing literal each iteration should get a universal proof");
        assert_eq!(proof.arity, 2);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");

        assert!(compile::try_compile(&s, h).is_some());
    }

    #[test]
    fn a_closure_created_in_a_leafs_own_top_level_expression_gets_a_universal_proof() {
        // rec f n = if n <= 0 then 0 else (\y. n+y)(5) + f(n-1) -- the
        // closure creation+call sits in the leaf's own top-level
        // expression (combined arithmetically with the recursive call),
        // not nested inside a self-call's own argument list --
        // find_self_calls/denote_with_placeholders now cover this too
        // (mirroring denote_closure_typed's own Term::Abs | Term::Rec
        // handling), not just a self-call argument's own closure creation.
        let mut s = TermStore::new();
        let y = s.var(0);
        let n_captured = s.var(1);
        let sum = s.prim(PrimOp::Add, n_captured, y);
        let closure = s.abs(sum);
        let five = s.lit(5);
        let call = s.app(closure, five);
        let n = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let f = s.var(1);
        let rec_call = s.app(f, n_minus_1);
        let sum2 = s.prim(PrimOp::Add, call, rec_call);
        let body = s.if_(cond, zero, sum2);
        let abs = s.abs(body);
        let h = s.rec(abs);

        let proof = prove_tail_recursive_universal(&s, h)
            .expect("a closure created in a leaf's own top-level expression should get a universal proof");
        assert_eq!(proof.arity, 1);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");

        assert!(compile::try_compile(&s, h).is_some());
    }

    #[test]
    fn a_closure_typed_loop_carried_parameter_compiles_and_is_kernel_verified() {
        // Cross-check against compile.rs/jit.rs directly, with an actual
        // closure argument (`inc`) baked into the term the same way
        // `twice_inc_5_gets_a_kernel_checked_closure_proof` does (there's
        // no way to pass a `Clo` value as a top-level runtime `i64`
        // argument -- see `jit.rs`'s own calling convention): this shape
        // already compiled before this proof extension existed
        // (`infer_closure_arities`/`compile_node`'s Var-callee branch
        // already handled a Clo-typed loop-carried parameter generically),
        // it just had no proof strategy covering it -- now two do: this
        // *particular* term also happens to get `is_kernel_verified` via
        // `prove_closure_expr` directly (`applied` itself is a direct,
        // fully-saturated call to the self-recursive combinator `it`,
        // which `prove_closure_expr`'s own `Term::Rec` widening covers --
        // see a_directly_called_self_recursive_combinator_gets_a_closure_proof
        // below for the same shape without a closure-typed parameter
        // involved), independently of `prove_tail_recursive_universal`'s
        // own new coverage that
        // `a_closure_typed_loop_carried_parameter_gets_a_universal_proof`
        // above exercises directly against `it` itself.
        let mut s = TermStore::new();
        let it = iterate(&mut s);
        let i = inc(&mut s);
        let five = s.lit(5);
        let three = s.lit(3);
        let it_3_i = s.app2(it, three, i);
        let applied = s.app(it_3_i, five); // iterate(3, inc, 5) = 8

        let mut jit = crate::jit::JitEngine::new();
        let result = jit.apply(&s, applied, &[]).unwrap();
        assert_eq!(result, 8);
        let interpreted = eval::apply_term(&s, applied, &[]).unwrap();
        assert_eq!(result, interpreted);
        assert!(jit.is_kernel_verified(applied));
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
    fn an_if_nested_inside_an_arithmetic_leaf_gets_a_universal_proof() {
        // rec f n = if n <= 0 then (n + (if n == 0 then 1 else 2)) else f(n-1)
        // -- the base leaf has an `If` embedded as a *sub-expression* of a
        // `Prim`, not as the whole body of some branch, so `classify_tree`
        // doesn't extract it into the DecisionTree itself; it stays part
        // of the leaf's own expression instead, and (with no self-call
        // inside it here) `find_self_calls`/`denote_with_placeholders`
        // just walk through it the same way they already walk a `Prim`.
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

        let proof = prove_tail_recursive_universal(&s, g).expect("a purely-arithmetic nested If should get a universal proof");
        assert_eq!(proof.arity, 1);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");
    }

    #[test]
    fn a_self_call_inside_a_nested_if_branch_gets_a_universal_proof_and_a_correct_instance() {
        // rec f n = if n <= 0 then 0
        //           else n + (if n mod 2 == 0 then f(n-1) else f(n-1) + 1)
        // -- the recursive leaf's own `If` isn't the whole branch body
        // either (it's the right-hand operand of the outer `+`), and this
        // time each of its two branches contains its own self-call
        // occurrence: `find_self_calls` must find both (in the same
        // left-to-right order `denote_with_placeholders` substitutes them
        // in), each becoming its own placeholder of the leaf's `combine`
        // function.
        let mut s = TermStore::new();
        let n = s.var(0);
        let f = s.var(1);
        let zero = s.lit(0);
        let outer_cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let two = s.lit(2);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let call = s.app(f, n_minus_1);
        let odd_branch = s.prim(PrimOp::Add, call, one);
        let n_mod_2 = s.prim(PrimOp::Mod, n, two);
        let inner_cond = s.prim(PrimOp::Eq, n_mod_2, zero);
        let inner_if = s.if_(inner_cond, call, odd_branch);
        let base_leaf = s.prim(PrimOp::Add, n, inner_if);
        let body = s.if_(outer_cond, zero, base_leaf);
        let abs = s.abs(body);
        let g = s.rec(abs);

        let proof = prove_tail_recursive_universal(&s, g).expect("a nested If with a self-call in each branch should still get a universal proof");
        assert_eq!(proof.arity, 1);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");

        // f(0)=0, f(1)=1+(f(0)+1)=2, f(2)=2+f(1)=4, f(3)=3+(f(2)+1)=8,
        // f(4)=4+f(3)=12, f(5)=5+(f(4)+1)=18.
        assert_eq!(eval::apply_term(&s, g, &[5]).unwrap(), 18, "interpreter sanity check");

        let instance = prove_tail_recursive_instance(&s, g, &[5]).expect("f(5) should get an instance");
        kernel::check(&instance.ctx, &instance.proof, &kernel::id(instance.int_ty.clone(), instance.lhs.clone(), instance.rhs.clone()))
            .expect("the recorded instance proof should independently re-typecheck");
    }

    #[test]
    fn a_clo_typed_nested_if_as_a_direct_self_call_argument_gets_a_universal_proof() {
        // rec f n g h = if n <= 0 then 0
        //               else f(n-1, (if n mod 2 == 0 then g else h), h) + g(n) + h(n)
        // -- `chosen = if n mod 2 == 0 then g else h` is a self-call's own
        // argument (threaded into the next iteration's `g` slot), and both
        // branches are `Clo`-typed parameters, not `Int`s -- exercises
        // `denote_closure_typed`'s widened `Term::If` arm (mirroring
        // `denote_closure`'s three-way Int/Int-or-Clo/Clo match via
        // `ite_clo_ref`), which builds each self-call argument's own
        // denotation for the leaf's `Ev` constructor. `g`/`h` are each
        // called directly (`g(n)`/`h(n)`) so `infer_closure_arities`
        // classifies both as `Clo`-typed arity-1 parameters in the first
        // place.
        let mut s = TermStore::new();
        let n = s.var(2);
        let g = s.var(1);
        let h = s.var(0);
        let f = s.var(3);

        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let two = s.lit(2);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let n_mod_2 = s.prim(PrimOp::Mod, n, two);
        let inner_cond = s.prim(PrimOp::Eq, n_mod_2, zero);
        let chosen = s.if_(inner_cond, g, h);

        let f_n1 = s.app(f, n_minus_1);
        let f_n1_chosen = s.app(f_n1, chosen);
        let self_call = s.app(f_n1_chosen, h);

        let call_g_n = s.app(g, n);
        let call_h_n = s.app(h, n);
        let sum1 = s.prim(PrimOp::Add, self_call, call_g_n);
        let leaf = s.prim(PrimOp::Add, sum1, call_h_n);

        let body = s.if_(cond, zero, leaf);
        let b1 = s.abs(body);
        let b2 = s.abs(b1);
        let abs = s.abs(b2);
        let top = s.rec(abs);

        let proof = prove_tail_recursive_universal(&s, top)
            .expect("a Clo-typed nested If as a direct self-call argument should get a universal proof");
        assert_eq!(proof.arity, 3);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");
    }

    #[test]
    fn a_clo_typed_nested_if_as_an_ad_hoc_closures_own_argument_gets_a_universal_proof() {
        // rec f n g g2 x =
        //   if n <= 0 then x
        //   else g(0) + g2(0) + (\h. h(x))(if n mod 2 == 0 then g else g2)
        //        + f(n-1, g, g2, x)
        // -- unlike the test above, the nested If here isn't a self-call's
        // own argument (find_self_calls's early self-call match would
        // consume the whole call node before ever walking into it); it's
        // the argument to an ad-hoc closure (`\h. h(x)`, itself capturing
        // `x` and calling its own `h` parameter, so `h` is itself
        // Clo-typed) created and called within the leaf, *alongside* a
        // separate, visible self-call in the same leaf's `Prim` tree. This
        // exercises `denote_with_placeholders`'s own widened `Term::If`
        // arm -- the leaf-specific walker that builds the leaf's `combine`
        // function body -- rather than `denote_closure_typed`'s. `g`/`g2`
        // are each called directly (`g(0)`/`g2(0)`) purely so
        // `infer_closure_arities` classifies both as `Clo`-typed.
        let mut s = TermStore::new();
        let n = s.var(3);
        let g = s.var(2);
        let g2 = s.var(1);
        let x = s.var(0);
        let f = s.var(4);

        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let two = s.lit(2);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let n_mod_2 = s.prim(PrimOp::Mod, n, two);
        let inner_cond = s.prim(PrimOp::Eq, n_mod_2, zero);
        let chosen = s.if_(inner_cond, g, g2);

        let call_g0 = s.app(g, zero);
        let call_g20 = s.app(g2, zero);
        let ab = s.prim(PrimOp::Add, call_g0, call_g20);

        // `\h. h(x)`, capturing `x` (Var(1) inside the closure's own
        // body, shifted by `h`'s own binder), h itself Clo-typed since
        // it's called right there.
        let h_var = s.var(0);
        let x_in_closure = s.var(1);
        let h_call = s.app(h_var, x_in_closure);
        let closure = s.abs(h_call);
        let closure_applied = s.app(closure, chosen);

        let abc = s.prim(PrimOp::Add, ab, closure_applied);

        let f_n1 = s.app(f, n_minus_1);
        let f_n1_g = s.app(f_n1, g);
        let f_n1_g_g2 = s.app(f_n1_g, g2);
        let self_call = s.app(f_n1_g_g2, x);

        let leaf = s.prim(PrimOp::Add, abc, self_call);
        let body = s.if_(cond, x, leaf);

        let b1 = s.abs(body);
        let b2 = s.abs(b1);
        let b3 = s.abs(b2);
        let abs = s.abs(b3);
        let top = s.rec(abs);

        let proof = prove_tail_recursive_universal(&s, top).expect(
            "a Clo-typed nested If used as an ad-hoc closure's own argument, alongside a separate self-call in the same leaf, should get a universal proof",
        );
        assert_eq!(proof.arity, 4);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");
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

    /// `rec f n = if n <= 1 then 1 else n * f(n-1)`, factorial -- used below
    /// as a named self-recursive combinator, the same way `twice`/`inc` are
    /// used as non-recursive ones.
    fn fact(s: &mut TermStore) -> Hash {
        let n = s.var(0);
        let f = s.var(1);
        let one = s.lit(1);
        let cond = s.prim(PrimOp::Le, n, one);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(f, n_minus_1);
        let else_branch = s.prim(PrimOp::Mul, n, rec_call);
        let body = s.if_(cond, one, else_branch);
        let abs = s.abs(body);
        s.rec(abs)
    }

    #[test]
    fn a_directly_called_self_recursive_combinator_gets_a_closure_proof() {
        // fact(10) -- a direct static call to a self-recursive combinator,
        // the App-root `Term::Rec` branch (mirroring the `Term::Abs`
        // direct-call path `twice_inc_5` already exercises): the call is
        // postulated opaque either way, so widening the pattern needed no
        // new proof machinery.
        let mut s = TermStore::new();
        let f = fact(&mut s);
        let ten = s.lit(10);
        let applied = s.app(f, ten);

        let proof = prove_closure_expr(&s, applied).expect("fact(10) should get a closure proof");
        assert_eq!(proof.arity, 0);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        assert!(compile::try_compile(&s, applied).is_some());
    }

    #[test]
    fn a_self_recursive_combinator_used_as_a_value_gets_a_closure_proof() {
        // (\g. g 10) fact -- what `let fact = rec f n = .. in fact 10`
        // desugars to (found via the REPL -- see syntax.rs/repl.rs, and
        // jit::tests::a_let_bound_self_recursive_function_compiles_and_is_kernel_verified
        // for the same shape checked directly against jit.rs): `fact`
        // itself, a bare `Term::Rec` value, gets registered
        // (`ClosureCombinators::register`) the same way a non-recursive
        // literal does, then called through `wrapper`'s own closure-typed
        // parameter via call_indirect.
        let mut s = TermStore::new();
        let f = fact(&mut s);
        let g = s.var(0);
        let ten = s.lit(10);
        let call_g = s.app(g, ten);
        let wrapper = s.abs(call_g);
        let applied = s.app(wrapper, f);

        let proof = prove_closure_expr(&s, applied).expect("(\\g. g 10) fact should get a closure proof");
        assert_eq!(proof.arity, 0);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        assert!(compile::try_compile(&s, applied).is_some());
    }

    #[test]
    fn a_partially_applied_self_recursive_combinator_used_as_a_value_gets_a_closure_proof() {
        // fact(1) supplied as a 1-of-1 partial application isn't a
        // meaningful example on its own (fact's arity is already 1), so
        // use a 2-ary self-recursive combinator instead: rec f n acc =
        // if n <= 0 then acc else f(n-1, n*acc); partial = f(3) (under-
        // applied by one arg); caller = \g. g(1); top = caller(partial).
        // pap_ref no longer rejects a recursive root -- compile::peel/
        // compile::free_vars/param_types_for were already generic over
        // is_rec (a call is always postulated opaque regardless), and
        // compile.rs's own register_partial_app/emit_pap_wrapper never
        // special-cased it either (a PAP wrapper only ever forwards a
        // static call to its root, indifferent to whether that root's own
        // codegen happens to loop), so the only thing standing in the way
        // was pap_ref's own extra is_rec check.
        let mut s = TermStore::new();
        let acc = s.var(0);
        let n = s.var(1);
        let f = s.var(2);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let n_times_acc = s.prim(PrimOp::Mul, n, acc);
        let rec_call = s.app2(f, n_minus_1, n_times_acc);
        let body = s.if_(cond, acc, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        let fact2 = s.rec(abs);

        let three = s.lit(3);
        let partial = s.app(fact2, three);

        let g = s.var(0);
        let one2 = s.lit(1);
        let call_g = s.app(g, one2);
        let caller = s.abs(call_g);

        let top = s.app(caller, partial);

        let proof = prove_closure_expr(&s, top)
            .expect("a partially applied self-recursive combinator used as a value should get a closure proof");
        assert_eq!(proof.arity, 0);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        assert!(compile::try_compile(&s, top).is_some());
    }

    #[test]
    fn partial_application_of_a_capturing_self_recursive_combinator_gets_a_closure_proof() {
        // The two pap_ref restrictions lifted independently this session
        // (a capturing root, then a self-recursive root) combined in one
        // term, to confirm they actually compose rather than each having
        // only been checked in isolation: \z. caller(fact2(3)) where
        // fact2 = rec f n acc = if n <= 0 then acc else f(n-1, n*acc+z)
        // captures z from the *enclosing* scope (not one of fact2's own
        // parameters), and is itself partially applied (one arg short) --
        // caller = \g. g(1) as before.
        let mut s = TermStore::new();
        let acc = s.var(0);
        let n = s.var(1);
        let f = s.var(2);
        let z = s.var(3); // captured from the enclosing \z. scope, not one of fact2's own params
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let n_times_acc = s.prim(PrimOp::Mul, n, acc);
        let plus_z = s.prim(PrimOp::Add, n_times_acc, z);
        let rec_call = s.app2(f, n_minus_1, plus_z);
        let body = s.if_(cond, acc, rec_call);
        let acc_abs = s.abs(body);
        let n_abs = s.abs(acc_abs);
        let fact2 = s.rec(n_abs);

        let three = s.lit(3);
        let partial = s.app(fact2, three);

        let g = s.var(0);
        let one2 = s.lit(1);
        let call_g = s.app(g, one2);
        let caller = s.abs(call_g);

        let top_inner = s.app(caller, partial);
        let top = s.abs(top_inner);

        let proof = prove_closure_expr(&s, top).expect(
            "a partially applied self-recursive combinator that also captures an outer variable should get a closure proof",
        );
        assert_eq!(proof.arity, 1);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        assert!(compile::try_compile(&s, top).is_some());
    }

    #[test]
    fn recursion_combined_with_closures_is_out_of_scope() {
        // Even a trivial Rec wrapper puts a closures term out of scope for
        // prove_closure_expr when it's the *top-level* term itself that's
        // Rec-wrapped (unlike a self-recursive combinator called or used
        // as a value *inside* an otherwise non-recursive top-level term --
        // see a_self_recursive_combinator_used_as_a_value_gets_a_closure_proof
        // and a_directly_called_self_recursive_combinator_gets_a_closure_proof
        // below for that, now-covered, case): prove_closure_expr's own
        // top-level check still requires `h` itself to be non-recursive,
        // since it's `build_universal`'s job, not this fragment's, to
        // prove what a self-recursive function's *own* body computes.
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
    fn inconsistent_call_arity_for_a_parameter_is_still_out_of_scope_for_the_closure_proof() {
        // \f. f(1) + f(1, 2) -- `f`, a *parameter*, called with
        // inconsistent arities (1 then 2) at different call sites -- same
        // adversarial shape as
        // compile::tests::inconsistent_call_arity_for_a_parameter_is_still_rejected.
        // Unrelated to partial application of a *literal lambda* (see
        // a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof
        // below for that, now-covered, case): param_types_for/
        // infer_closure_arities already reject an inconsistent-arity
        // parameter outright, before denote_closure's own PAP handling
        // (which only ever applies to a literal Abs root) ever comes into
        // play.
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
    fn a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof() {
        // add = \x y. x + y; partial = add(3) (under-applied by one
        // argument); caller = \g. g(4); top = caller(partial) -- same
        // shape as compile::tests::partial_application_of_a_literal_lambda_compiles.
        // `partial` is denoted via pap_ref's new `Less`-arity branch (a
        // Clo-typed value), then completed through caller's own
        // call_indirect the same way any other Clo-typed argument would be.
        let mut s = TermStore::new();
        let x = s.var(1);
        let y = s.var(0);
        let sum = s.prim(PrimOp::Add, x, y);
        let inner_add = s.abs(sum);
        let add = s.abs(inner_add);

        let three = s.lit(3);
        let partial = s.app(add, three);

        let g = s.var(0);
        let four = s.lit(4);
        let call_g = s.app(g, four);
        let caller = s.abs(call_g);

        let top = s.app(caller, partial);

        let proof = prove_closure_expr(&s, top).expect("a partially applied literal lambda used as a value should get a closure proof");
        assert_eq!(proof.arity, 0);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        // Also actually compiles, and the two readings agree on scope.
        assert!(compile::try_compile(&s, top).is_some());
    }

    #[test]
    fn a_partially_applied_literal_lambda_with_mixed_parameter_types_gets_a_closure_proof() {
        // caller2(twice(inc)) -- `twice`'s own param_types are
        // [None(x), Some(1)(f)] (mixed: x plain Int, f closure-typed),
        // unlike the add-based test above where both parameters happen to
        // be Int and so can't distinguish a correct `pap_ref` type slice
        // from an incorrectly-shifted one. Supplying only `f` (`inc`) is a
        // 1-of-2 partial application, so pap_ref's type must be built from
        // param_types[arity-k..] = param_types[1..2] = [Some(1)] (f's own
        // Clo type) -- not param_types[..k] = param_types[0..1] (x's Int
        // type, wrong parameter entirely). caller2 = \h. h(5) then
        // completes the wrapper with the missing `x` argument.
        let mut s = TermStore::new();
        let t = twice(&mut s);
        let i = inc(&mut s);
        let partial = s.app(t, i); // twice(inc) -- under-applied by one arg (x)

        let h = s.var(0);
        let five = s.lit(5);
        let call_h = s.app(h, five);
        let caller2 = s.abs(call_h);

        let top = s.app(caller2, partial);

        let proof = prove_closure_expr(&s, top).expect("a partially applied combinator with mixed parameter types should get a closure proof");
        assert_eq!(proof.arity, 0);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        assert!(compile::try_compile(&s, top).is_some());
    }

    #[test]
    fn a_partially_applied_capturing_literal_lambda_used_as_a_value_gets_a_closure_proof() {
        // g = \z. (\g2. g2(4)) ((\x y. x + y + z)(3)) -- same shape as
        // compile::tests::partial_application_of_a_capturing_literal_lambda_compiles,
        // which compiles via push_pap_env composing the wrapper's own
        // environment with a copy of the (capturing) root's own
        // environment. pap_ref now mirrors that: when the root captures,
        // its postulated type takes the root's own Env as a leading
        // parameter (the same convention call_ref already uses), and every
        // PAP call site builds that environment via build_env_expr and
        // prepends it to the wrapper's own arguments -- so this now gets a
        // kernel-checked proof too, not just empirical sample verification.
        let mut s = TermStore::new();
        let y = s.var(0);
        let x = s.var(1);
        let z_captured = s.var(2);
        let xy = s.prim(PrimOp::Add, x, y);
        let xyz = s.prim(PrimOp::Add, xy, z_captured);
        let inner = s.abs(xyz);
        let capturing_add = s.abs(inner);

        let three = s.lit(3);
        let partial = s.app(capturing_add, three);

        let g2 = s.var(0);
        let four = s.lit(4);
        let call_g2 = s.app(g2, four);
        let caller = s.abs(call_g2);

        let called = s.app(caller, partial);
        let g = s.abs(called);

        let proof = prove_closure_expr(&s, g).expect("a partially applied capturing literal lambda used as a value should get a closure proof");
        assert_eq!(proof.arity, 1);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        assert!(compile::try_compile(&s, g).is_some());
    }

    #[test]
    fn over_application_of_a_literal_lambda_is_still_out_of_scope_for_the_closure_proof() {
        // add = \x y. x + y, called with three arguments -- rejected by
        // denote_closure's own args.len() > arity check (proof.rs has no
        // fragment for over-application at all, unlike compile.rs, which
        // now compiles the shape -- see compile.rs's own module docs and
        // compile::tests::an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter
        // -- though not *this* term specifically: `add`'s body is a plain
        // `Int`, never a further closure, so this one is genuinely
        // ill-typed and would only ever be trusted via jit.rs's own
        // sample verification, never a kernel-checked proof).
        let mut s = TermStore::new();
        let x = s.var(1);
        let y = s.var(0);
        let sum = s.prim(PrimOp::Add, x, y);
        let inner_add = s.abs(sum);
        let add = s.abs(inner_add);

        let one = s.lit(1);
        let two = s.lit(2);
        let three = s.lit(3);
        let partial = s.app2(add, one, two);
        let over_applied = s.app(partial, three);

        assert!(prove_closure_expr(&s, over_applied).is_none());
    }

    #[test]
    fn calling_a_literal_lambda_whose_own_body_picks_between_two_closures_gets_a_closure_proof() {
        // \x. (\g. g 5) (if 0 < x then (\y. x + y) else (\y. x - y)) --
        // the same term compile.rs's own
        // a_capturing_closure_compiles_and_matches_interpreter test uses.
        // `picker` (whose own body is the If) is *directly called*
        // (`chosen = picker(x2)`, a fully-saturated application of a
        // literal lambda) -- `call_ref`'s own postulated type used to
        // always assume a directly-called combinator returns `Int`,
        // causing `chosen`'s claimed `Int` type to fail `inn`'s own
        // `.clo()?` check where it's used as `g`. `call_ref` now consults
        // `combinator_return_type` for its own return type instead of
        // universally assuming `Int` -- correctly classifying `picker`'s
        // body (an `If` between two closures) as `Clo`-typed, without
        // `call_ref` itself ever denoting `picker`'s own body -- so this
        // now gets a genuine kernel-checked proof.
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
        let proof = prove_closure_expr(&s, f).expect("picker's own Clo-typed body should now be reachable through call_ref");
        assert_eq!(proof.arity, 1);
        kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
            .expect("the recorded proof should independently re-typecheck");
    }

    #[test]
    fn a_literal_lambda_picking_between_two_different_arity_closures_is_out_of_scope() {
        // Same shape as the test above -- `\x. (\g. g 5) (if 0 < x then
        // (\y. x + y) else (\y. \z. x - y - z))` -- except `picker`'s own
        // `else` branch now has arity *2*, not 1: `Clo`, before the
        // arity-indexed `Clo_k` refactor (`TYPES.md` section 7), was a
        // single, arity-blind kernel type, so this exact shape would have
        // kernel-*typechecked* under the old scheme (`ite_clo : Int -> Clo
        // -> Clo -> Clo` accepts any two `Clo`-typed branches, whatever
        // their underlying arity) while being genuinely unsound --
        // `inn`'s own `g 5` call commits to arity 1, silently wrong
        // whenever `picker` actually took the `else` branch. Both
        // `return_type_of`'s own arity-consistency check (in
        // `combinator_return_type`'s classification of `picker`'s body)
        // and, independently, `kernel::check`'s definitional-inequality
        // between `Clo_1` and `Clo_2` now reject this -- `call_ref` falls
        // back to assuming `picker`'s call is plain `Int`-typed (the
        // classifier can't determine a single consistent arity), which
        // then fails `inn`'s own `.clo()?` check on `g`, so
        // `prove_closure_expr` returns `None` rather than a
        // kernel-"verified" but unsound proof.
        let mut s = TermStore::new();
        let x = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, x);
        let y_pos = s.var(0);
        let x_pos = s.var(1);
        let plus = s.prim(PrimOp::Add, x_pos, y_pos);
        let then_closure = s.abs(plus); // arity 1: \y. x + y
        let z_neg = s.var(0);
        let y_neg = s.var(1);
        let x_neg = s.var(2);
        let x_minus_y = s.prim(PrimOp::Sub, x_neg, y_neg);
        let minus_z = s.prim(PrimOp::Sub, x_minus_y, z_neg);
        let else_inner = s.abs(minus_z);
        let else_closure = s.abs(else_inner); // arity 2: \y. \z. x - y - z
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

        assert!(
            prove_closure_expr(&s, f).is_none(),
            "an If between two different-arity closures should be rejected, not accepted as a single blind Clo"
        );
    }

    #[test]
    fn an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof() {
        // f = \a b. if 0 < a then (\c. a+b+c) else (\c. a-b+c); f(a,b,c) --
        // same shape as compile::tests::
        // an_over_applied_literal_lambda_returning_a_closure_compiles_and_matches_interpreter/
        // jit::tests::an_over_applied_literal_lambda_returning_a_closure_compiles_and_is_kernel_verified.
        // Unlike the test above (a directly-called combinator's own
        // Clo-typed result used as a *value*), this is genuine
        // over-application: `f`'s own saturated call (`f(a,b)`) is
        // denoted first via `call_ref` (now correctly `Clo`-typed, same
        // classifier), then dispatched on the extra argument `c` through
        // `apply_ref`, exactly the way calling a closure-typed variable
        // already denotes.
        let mut s = TermStore::new();
        let c1 = s.var(0);
        let b1 = s.var(1);
        let a1 = s.var(2);
        let ab1 = s.prim(PrimOp::Add, a1, b1);
        let abc1 = s.prim(PrimOp::Add, ab1, c1);
        let closure1 = s.abs(abc1);

        let c2 = s.var(0);
        let b2 = s.var(1);
        let a2 = s.var(2);
        let amb2 = s.prim(PrimOp::Sub, a2, b2);
        let ambc2 = s.prim(PrimOp::Add, amb2, c2);
        let closure2 = s.abs(ambc2);

        let a_body = s.var(1);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, a_body);
        let body = s.if_(cond, closure1, closure2);
        let b_binder = s.abs(body);
        let f = s.abs(b_binder);

        let a_param = s.var(2);
        let b_param = s.var(1);
        let c_param = s.var(0);
        let fa = s.app(f, a_param);
        let fab = s.app(fa, b_param);
        let fabc = s.app(fab, c_param);
        let c_binder = s.abs(fabc);
        let bc_binder = s.abs(c_binder);
        let top = s.abs(bc_binder);

        assert_eq!(eval::apply_term(&s, top, &[10, 3, 100]).unwrap(), 113, "interpreter sanity check");
        assert_eq!(eval::apply_term(&s, top, &[-5, 3, 100]).unwrap(), 92, "interpreter sanity check");

        let proof = prove_closure_expr(&s, top).expect("an over-applied literal lambda returning a closure should get a proof");
        assert_eq!(proof.arity, 3);
        kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
            .expect("the recorded proof should independently re-typecheck");
    }

    #[test]
    fn a_capturing_closure_used_as_a_value_gets_a_closure_proof() {
        // g = \x. (\h. h 5) (\y. x + y) -- `\y. x + y` captures `x`, g's
        // own parameter, and is used as a plain *value* (an argument to
        // `\h. h 5`), not directly called -- exercises
        // ClosureCombinators::register's new mk_clo_ref path and
        // build_env_expr together with the pre-existing apply_ref
        // (call-through-a-parameter) path, unmodified.
        let mut s = TermStore::new();
        let y = s.var(0);
        let x = s.var(1);
        let sum = s.prim(PrimOp::Add, x, y);
        let closure = s.abs(sum);

        let h = s.var(0);
        let five = s.lit(5);
        let call_h = s.app(h, five);
        let inn = s.abs(call_h);

        let applied = s.app(inn, closure);
        let g = s.abs(applied);

        let proof = prove_closure_expr(&s, g).expect("a capturing closure used as a value should get a proof now");
        assert_eq!(proof.arity, 1);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        for x_val in [-5, 0, 1, 42] {
            let interpreted = eval::apply_term(&s, g, &[x_val]).unwrap();
            assert_eq!(interpreted, x_val + 5, "sanity check on the term itself, not the proof");
        }
    }

    #[test]
    fn a_directly_called_capturing_closure_gets_a_closure_proof() {
        // g = \x. (\y. x + y) 5 -- `\y. x + y` captures g's own `x`, and
        // is called *directly* (a literal lambda in function position),
        // exercising call_ref's new Env-prefixed signature and
        // build_env_expr in the direct-call branch of denote_closure.
        let mut s = TermStore::new();
        let y = s.var(0);
        let x = s.var(1);
        let sum = s.prim(PrimOp::Add, x, y);
        let closure = s.abs(sum);
        let five = s.lit(5);
        let called = s.app(closure, five);
        let g = s.abs(called);

        let proof = prove_closure_expr(&s, g).expect("a directly called capturing closure should get a proof now");
        assert_eq!(proof.arity, 1);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");
    }

    #[test]
    fn a_capture_of_a_closure_typed_value_gets_a_closure_proof() {
        // g = \cb. cb(1) + (\h. h 5) (\y. cb) -- `cb(1)` makes g's own
        // scan recognize `cb` as closure-typed (Some(1)); `\y. cb`
        // separately captures that same `cb`. `build_env_expr`'s own
        // capture signature (`capture_sig`) now lets `Env`/`mk_env` hold
        // a `Clo`-typed slot honestly, rather than assuming every capture
        // is `Int` -- so this gets a proof.
        //
        // Note what this proof is (and isn't) claiming: `h`'s own call
        // (`h 5`, through `call_ref`, which -- like every opaque call in
        // this fragment -- always postulates an `Int` return) is used as
        // the `Prim::Add`'s own second operand, denoted `Int` accordingly.
        // The concrete closure actually bound to `h` here (`\y. cb`)
        // returns a `Clo`, not an `Int`, so this particular term always
        // errors at runtime on both readings (confirmed: interpreted and
        // compiled both return `Err(TypeError)`) -- but the proof was
        // never a runtime-correctness certificate to begin with: it's a
        // `refl` argument that both readings compose the *same* postulated
        // symbols identically, which holds regardless of what those
        // symbols are later found to compute. `jit.rs`'s own sample-based
        // `verify()` independently agrees this term is "verified" too,
        // in exactly the same weak sense (`Err == Err`) -- consistent,
        // not contradictory, and the same honest limitation `call_ref`'s
        // own always-`Int`-return assumption already has everywhere else
        // in this fragment.
        let mut s = TermStore::new();
        let cb1 = s.var(0);
        let one = s.lit(1);
        let call_cb = s.app(cb1, one);

        let cb_captured = s.var(1); // \y. cb -- ignores y, returns the captured cb
        let closure = s.abs(cb_captured);

        let h = s.var(0);
        let five = s.lit(5);
        let call_h = s.app(h, five);
        let inn = s.abs(call_h);

        let applied = s.app(inn, closure);
        let body = s.prim(PrimOp::Add, call_cb, applied);
        let g = s.abs(body);

        let proof =
            prove_closure_expr(&s, g).expect("a capture of a closure-typed value should get a closure proof");
        assert_eq!(proof.arity, 1);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        assert!(compile::try_compile(&s, g).is_some());
    }

    #[test]
    fn a_closure_created_in_a_self_call_argument_capturing_a_closure_typed_loop_parameter_gets_a_universal_proof() {
        // rec f n g x = if n <= 0 then x else f(n-1, g, g x + (\y. g y + 1) x)
        // -- same closure-typed loop-carried parameter as `iterate`, but
        // each iteration *also* creates a fresh closure (`\y. g y + 1`)
        // that captures `g` itself (a `Clo`-typed value, not an `Int`).
        // The direct call `g x` is still needed here, unrelated to the
        // capture itself: `infer_closure_arities` never looks inside a
        // nested `Abs`'s own body (a lambda used as a plain value is
        // opaque to it, matching `denote_closure`'s own "a call is never
        // denoted by looking inside a body" discipline one level up), so
        // without *some* direct call to `g` at `it`'s own top level, `g`
        // would never be classified `Clo`-typed at all and this wouldn't
        // exercise the capture-typing question -- it would just be
        // rejected (or silently misclassified) for an unrelated reason.
        //
        // Exercises `denote_closure_typed`'s own value-leaf registration
        // with a `Clo`-typed capture, inside `build_universal`'s full
        // induction pipeline (not just the non-recursive `prove_closure_expr`
        // fragment `a_capture_of_a_closure_typed_value_gets_a_closure_proof`
        // above checks).
        let mut s = TermStore::new();
        let x = s.var(0);
        let g = s.var(1);
        let n = s.var(2);
        let f = s.var(3);

        let gx = s.app(g, x);

        let y = s.var(0);
        let g_captured = s.var(2); // g, shifted by the wrapper's own y binder
        let gy = s.app(g_captured, y);
        let one = s.lit(1);
        let gy_plus_1 = s.prim(PrimOp::Add, gy, one);
        let wrapper = s.abs(gy_plus_1);
        let wrapper_call = s.app(wrapper, x);

        let new_x = s.prim(PrimOp::Add, gx, wrapper_call);

        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one2 = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one2);
        let f_n1_g = s.app2(f, n_minus_1, g);
        let rec_call = s.app(f_n1_g, new_x);
        let body = s.if_(cond, x, rec_call);
        let g_binder = s.abs(body);
        let n_binder = s.abs(g_binder);
        let abs = s.abs(n_binder);
        let it = s.rec(abs);

        let proof = prove_tail_recursive_universal(&s, it)
            .expect("a closure created in a self-call argument capturing a closure-typed loop parameter should get a universal proof");
        assert_eq!(proof.arity, 3);
        kernel::check(&proof.ctx, &proof.theorem_proof, &proof.theorem_ty)
            .expect("the recorded theorem should independently re-typecheck");

        // inc = \y. y + 1, baked in as the initial g, run for real: each
        // iteration computes new_x = g(x) + (g(x)+1) = 2*inc(x) + 1 =
        // 2x + 3. Starting from x=0: 3, 9, 21, 45, 93 after 1..5
        // iterations (hand-derived and cross-checked against eval::apply_term
        // directly while building this test).
        let y2 = s.var(0);
        let one3 = s.lit(1);
        let inc_body = s.prim(PrimOp::Add, y2, one3);
        let inc = s.abs(inc_body);
        let n_lit = s.lit(5);
        let x0 = s.lit(0);
        let partial = s.app2(it, n_lit, inc);
        let top = s.app(partial, x0);

        assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 93);
        assert!(compile::try_compile(&s, top).is_some());
    }

    #[test]
    fn a_whole_functions_result_being_a_closure_is_still_out_of_scope() {
        // \x. if x > 0 then inc else inc -- an `If` choosing between two
        // closures is *not* the restriction that rejects this one anymore
        // (denote_closure's own `Term::If` now covers Clo branches via
        // `ite_clo` -- see a_closure_typed_ifs_own_result_used_as_a_value_gets_a_closure_proof
        // below for that, now-covered, case): this term's own rejection
        // reason is orthogonal -- `f`'s own body (the whole function's
        // result) denotes as `Clo`, not `Int`, and prove_closure_expr's
        // top-level call always requires `Int` there, closures or not.
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

    /// `\z. z - 1`.
    fn dec(s: &mut TermStore) -> Hash {
        let z = s.var(0);
        let one = s.lit(1);
        let z_minus_1 = s.prim(PrimOp::Sub, z, one);
        s.abs(z_minus_1)
    }

    #[test]
    fn a_closure_typed_ifs_own_result_used_as_a_value_gets_a_closure_proof() {
        // \w. caller(if 0 < w then inc else dec, 5) where
        // caller = \g x. g(x) -- the If's own result (Denoted::Clo, via
        // the new `ite_clo` postulate) is used as caller's *argument*
        // (matching caller's own closure-typed parameter `g`), not as a
        // directly-called combinator's implicit return -- exactly the
        // shape `ite_clo` actually needs to be reachable (see
        // calling_a_literal_lambda_whose_own_body_picks_between_two_closures_is_still_out_of_scope
        // above for the shape that still isn't).
        let mut s = TermStore::new();
        let x = s.var(0);
        let g = s.var(1);
        let call_gx = s.app(g, x);
        let caller_inner = s.abs(call_gx);
        let caller = s.abs(caller_inner);

        let w = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, w);
        let i = inc(&mut s);
        let d = dec(&mut s);
        let picked = s.if_(cond, i, d);
        let five = s.lit(5);
        let top = s.app2(caller, picked, five);
        let f = s.abs(top);

        let proof = prove_closure_expr(&s, f).expect("an If between two closures used as a value should get a closure proof");
        assert_eq!(proof.arity, 1);
        kernel::check(
            &proof.ctx,
            &proof.proof,
            &kernel::id(proof.int_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        assert!(compile::try_compile(&s, f).is_some());
    }

    #[test]
    fn an_if_mismatching_int_and_clo_branches_is_out_of_scope() {
        // \w. caller(if 0 < w then inc else 5, 5) -- one branch Clo
        // (`inc`), the other Int (`5`) -- neither ite_ref nor ite_clo
        // applies; rejected as a genuine type mismatch, not silently
        // accepted as either.
        let mut s = TermStore::new();
        let x = s.var(0);
        let g = s.var(1);
        let call_gx = s.app(g, x);
        let caller_inner = s.abs(call_gx);
        let caller = s.abs(caller_inner);

        let w = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, w);
        let i = inc(&mut s);
        let five_branch = s.lit(5);
        let picked = s.if_(cond, i, five_branch);
        let five = s.lit(5);
        let top = s.app2(caller, picked, five);
        let f = s.abs(top);

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
