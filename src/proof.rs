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
//! real induction on the call depth. At the time this was built, there
//! was no bare inductive `Nat` to induct on in this predicative kernel
//! (see `kernel`'s docs) -- `kernel::tests::
//! nat_via_w_is_a_genuinely_computing_inductive_type` has since shown a
//! real one is buildable from the kernel's own existing primitives alone
//! (predicativity was never actually the obstacle -- `WRec` already
//! supports eliminating into any `Sort(k)`), but wiring it in as a
//! replacement for the postulated family below is a separate, not yet
//! attempted follow-on (see `RELATED_WORK.md`) -- `Ev` itself is also an
//! *indexed* family (depends on `params`/`v`), which a plain `Nat`'s own
//! structural recursor doesn't directly hand you either way. So, for
//! now, `prove_tail_recursive_universal` postulates a
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
use std::collections::HashSet;
use std::rc::Rc;

use crate::compile;
use crate::eval;
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
/// (`prove_tail_recursive_call`, the tail-recursive fragment) -- both
/// always `Int`-typed, unlike `prove_closure_expr`'s own use of this same
/// struct, where `result_ty` may be `Int` or a `Clo_k` (a closure-typed
/// top-level result, e.g. `\x. \y. x+y` used bare).
pub struct EquivalenceProof {
    pub ctx: Ctx,
    pub arity: usize,
    pub result_ty: Expr,
    pub denotation: Expr,
    /// `: Id(result_ty, denotation, denotation)`.
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
    let result_ty = arith.int_ty();
    let proof = kernel::refl(denotation.clone());
    let proof_ty = kernel::id(result_ty.clone(), denotation.clone(), denotation.clone());
    kernel::check(&arith.p.ctx, &proof, &proof_ty).ok()?;

    Some(EquivalenceProof {
        ctx: arith.p.ctx,
        arity,
        result_ty,
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
// self-call argument, or one fed to a closure call, may also be a freshly
// *created* closure (`denote_closure_typed` mirrors `denote_closure`'s own
// `Term::Abs`/`Term::Rec` handling via the same `ClosureCombinators`), not
// just a bare parameter reference, and an `If` choosing between two
// `Clo`-typed values is in scope too (`ite_clo_ref`, same as
// `denote_closure`'s own) -- see `build_universal`'s own doc comment below
// for the one thing still out of scope here (a captured free variable).
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
#[derive(Clone)]
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
        match classify_app_node(store, h, param_types)? {
            AppShape::ParamCall { root, k, args } => {
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
            // `denote_closure_typed`'s own `AppShape::LitLambda*` arms
            // (and, through it, `denote_closure`'s) exactly, including its
            // `combinator_return_type`-gated over-application dispatch,
            // just checking for a self-call occurrence in each argument
            // first.
            AppShape::LitLambdaPartial { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
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
            AppShape::LitLambdaExact { root, args, callee_param_types } | AppShape::LitLambdaOver { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
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
        match classify_app_node(store, h, param_types)? {
            AppShape::ParamCall { root, k, args } => {
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
            // `AppShape::LitLambda*` arms exactly (same
            // direct-call/partial-application/over-application 3-way,
            // same `pap_ref`-still-rejects-a-recursive-root narrowing,
            // same `combinator_return_type`-gated over-application
            // dispatch), just against `combinators` directly instead of
            // through a wrapper.
            AppShape::LitLambdaPartial { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
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
            AppShape::LitLambdaExact { root, args, callee_param_types } | AppShape::LitLambdaOver { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
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
        match classify_app_node(store, h, param_types)? {
            AppShape::ParamCall { args, .. } => {
                for &a in &args {
                    prime_closure_postulates(store, a, self_call, param_types, combinators)?;
                }
                Some(())
            }
            AppShape::LitLambdaPartial { root, args, .. } => {
                combinators.pap_ref(root, args.len(), param_types)?;
                // `pap_ref` itself only primes the pap combinator's own
                // postulate, not the transitive `mk_env_ref` a capturing
                // root's own `build_env_expr` call will need -- that has
                // to be primed here too, the same way
                // `prime_direct_call` primes it below, or its first push
                // can still happen from inside a temporary
                // `params_and_close_typed` scope and go stale.
                let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
                let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
                if !root_captures.is_empty() {
                    let sig = capture_sig(&root_captures, param_types)?;
                    combinators.cp.mk_env_ref(&sig);
                }
                for &a in &args {
                    prime_closure_postulates(store, a, self_call, param_types, combinators)?;
                }
                Some(())
            }
            // Primes `call_ref` for root's own saturated call, shared
            // between an exact match and an over-application's own
            // leading portion (`prime_direct_call`); an over-application
            // also needs `apply_ref` primed for its own extra-argument
            // count -- whether the saturated call's result is actually
            // `Clo`-typed (required for the real denotation to accept
            // this at all -- see `combinator_return_type`) isn't checked
            // here, deliberately: priming just needs to cover every
            // postulate the real pass *might* touch, and an unneeded
            // prime for a term the real pass later rejects anyway is
            // harmless, not unsound.
            AppShape::LitLambdaExact { root, args, .. } => {
                prime_direct_call(store, root, param_types, combinators)?;
                for &a in &args {
                    prime_closure_postulates(store, a, self_call, param_types, combinators)?;
                }
                Some(())
            }
            AppShape::LitLambdaOver { root, args, callee_param_types } => {
                prime_direct_call(store, root, param_types, combinators)?;
                combinators.cp.apply_ref(args.len() - callee_param_types.len());
                for &a in &args {
                    prime_closure_postulates(store, a, self_call, param_types, combinators)?;
                }
                Some(())
            }
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

/// Primes `root`'s own `call_ref` postulate and, if it captures, the
/// transitive `mk_env_ref` its own environment construction will need --
/// shared by `prime_closure_postulates`' `AppShape::LitLambdaExact`/
/// `LitLambdaOver` arms (an over-application's own extra-argument
/// `apply_ref` priming is distinct per arm, so stays there).
fn prime_direct_call(store: &TermStore, root: Hash, param_types: &[Option<usize>], combinators: &mut ClosureCombinators<'_>) -> Option<()> {
    let (c_arity, c_body, c_is_rec) = compile::peel(store, root)?;
    let captures = compile::free_vars(store, c_body, c_arity, c_is_rec);
    combinators.call_ref(root, &captures, param_types)?;
    if !captures.is_empty() {
        let sig = capture_sig(&captures, param_types)?;
        combinators.cp.mk_env_ref(&sig);
    }
    Some(())
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
    // captured free variable -- `self_idx` sits just outside `0..arity`,
    // so a self-call's own callee position never gets misclassified as one
    // of these) is treated as `Clo`-typed throughout this function.
    // `denote_closure_typed` (used by `new_params_for` below) also covers
    // closure *creation* inside a self-call argument -- registering a
    // combinator, calling one directly, or partially applying one -- and a
    // nested `If` choosing between two `Clo`-typed values, both via the
    // same `ClosureCombinators` machinery `prove_closure_expr` itself uses.
    // Still out of scope: a captured free variable used as a closure here
    // (this function has no enclosing frame to resolve one against).
    let found = compile::infer_closure_arities(store, body, arity, Some(self_idx))?;
    // See `param_types_for`'s own docs: an inconsistently-called `Var` is
    // declined the same way an absent one already is.
    let param_types: Vec<Option<usize>> = (0..arity as u32)
        .map(|i| match found.get(&i) {
            Some(compile::ArityUse::Consistent(k)) => Some(*k),
            Some(compile::ArityUse::Inconsistent) | None => None,
        })
        .collect();

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
    // sites will need, and every `ite_clo_ref(k)` (see its own docs --
    // `clo_ty` eagerly primes it as a side effect, but `clo_ty` itself no
    // longer pushes anything of its own -- see `RELATED_WORK.md` section
    // 11 -- so `ite_clo_ref` is the only postulate left to worry about
    // staleness for here) that same parameter's own arity `k` will need,
    // *before* any of the temporary, later-rolled-back
    // `params_and_close_typed` scopes below gets a chance to trigger its
    // lazy push itself. This memoization
    // (`ClosurePostulates::apply_pos`/`ite_clo_pos`) was designed
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
    combinators: &mut ClosureCombinators<'_>,
    params: &[Anchored],
    concrete: &[i64],
    param_facts: &[Anchored],
) -> Option<(i64, Expr, Expr)> {
    if matches!(store.resolve(h), Term::App(..)) {
        // `param_types` is always empty here: every caller of this
        // function (via `instance_from_scaffold`'s own precondition) only
        // ever runs where the *outer* frame is entirely `Int`-typed, so
        // `AppShape::ParamCall` can never legitimately classify -- passing
        // `&[]` makes `classify_app_node`'s own `Var`-root case fail
        // cleanly (an out-of-range lookup), the same as an explicit
        // all-`None` array would, without needing to fabricate one.
        return match classify_app_node(store, h, &[])? {
            AppShape::LitLambdaExact { root, args, callee_param_types } => {
                eval_and_prove_call(store, root, &args, &callee_param_types, combinators, params, concrete, param_facts)
            }
            // `root`'s own saturated call returns a `Clo_k`, then the
            // extra arguments are dispatched against it via `apply_ref` --
            // see `eval_and_prove_call_over`'s own docs.
            AppShape::LitLambdaOver { root, args, callee_param_types } => {
                eval_and_prove_call_over(store, root, &args, &callee_param_types, combinators, params, concrete, param_facts)
            }
            // A `Clo`-typed result (`LitLambdaPartial`) has no concrete
            // representation at all (see `instance_from_scaffold`'s own
            // docs); `ParamCall` is structurally unreachable (see above).
            AppShape::ParamCall { .. } | AppShape::LitLambdaPartial { .. } => None,
        };
    }
    match store.resolve(h) {
        Term::Var(i) => {
            let i = *i as usize;
            Some((*concrete.get(i)?, params.get(i)?.at(&combinators.cp.arith), param_facts.get(i)?.at(&combinators.cp.arith)))
        }
        Term::Lit(n) => {
            let l = combinators.cp.arith.lit_ref(*n);
            Some((*n, l.clone(), kernel::refl(l)))
        }
        Term::Prim(op, a, b) => {
            let (op, a, b) = (*op, *a, *b);
            let (xa, da, pa) = eval_and_prove(store, a, combinators, params, concrete, param_facts)?;
            let da = Anchored::new(&combinators.cp.arith, da);
            let pa = Anchored::new(&combinators.cp.arith, pa);
            let (xb, db, pb) = eval_and_prove(store, b, combinators, params, concrete, param_facts)?;
            let db = Anchored::new(&combinators.cp.arith, db);
            let pb = Anchored::new(&combinators.cp.arith, pb);
            let fact = combinators.cp.arith.assume_prim_fact(op, xa, xb);
            let result = apply_prim_concrete(op, xa, xb);

            // Nothing pushes onto arith.p.ctx from here on, so resolving
            // everything fresh now (past `assume_prim_fact`'s own push)
            // keeps it all valid for the rest of this call.
            let (da, pa, db, pb) = (da.at(&combinators.cp.arith), pa.at(&combinators.cp.arith), db.at(&combinators.cp.arith), pb.at(&combinators.cp.arith));
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
            debug_assert_has_type(&combinators.cp.arith.p.ctx, &proof, &kernel::id(int_ty, lhs.clone(), rhs), "eval_and_prove: Prim proof");
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
            let (xc, dc, pc) = eval_and_prove(store, c, combinators, params, concrete, param_facts)?;
            let dc = Anchored::new(&combinators.cp.arith, dc);
            let pc = Anchored::new(&combinators.cp.arith, pc);
            let (xt, dt, pt) = eval_and_prove(store, t, combinators, params, concrete, param_facts)?;
            let dt = Anchored::new(&combinators.cp.arith, dt);
            let pt = Anchored::new(&combinators.cp.arith, pt);
            let (xe, de, pe) = eval_and_prove(store, e, combinators, params, concrete, param_facts)?;
            let de = Anchored::new(&combinators.cp.arith, de);
            let pe = Anchored::new(&combinators.cp.arith, pe);
            let fact = combinators.cp.arith.assume_ite_fact(xc, xt, xe);
            let result = if xc != 0 { xt } else { xe };

            let (dc, pc, dt, pt, de, pe) = (
                dc.at(&combinators.cp.arith),
                pc.at(&combinators.cp.arith),
                dt.at(&combinators.cp.arith),
                pt.at(&combinators.cp.arith),
                de.at(&combinators.cp.arith),
                pe.at(&combinators.cp.arith),
            );
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
            debug_assert_has_type(&combinators.cp.arith.p.ctx, &proof, &kernel::id(int_ty, lhs.clone(), rhs), "eval_and_prove: If proof");
            Some((result, lhs, proof))
        }
        Term::Abs(_) | Term::App(..) | Term::Rec(_) => None,
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
fn eval_and_prove_call(
    store: &TermStore,
    root: Hash,
    args: &[Hash],
    callee_param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[Anchored],
    concrete: &[i64],
    param_facts: &[Anchored],
) -> Option<(i64, Expr, Expr)> {
    if callee_param_types.iter().any(Option::is_some) {
        return None;
    }

    // Evaluate each argument in the *outer* frame, application order.
    let mut arg_triples = Vec::with_capacity(args.len());
    for &a in args {
        let (x, d, p) = eval_and_prove(store, a, combinators, params, concrete, param_facts)?;
        arg_triples.push((x, Anchored::new(&combinators.cp.arith, d), Anchored::new(&combinators.cp.arith, p)));
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
        let d = Anchored::new(&combinators.cp.arith, params.get(rel)?.at(&combinators.cp.arith));
        let p = Anchored::new(&combinators.cp.arith, param_facts.get(rel)?.at(&combinators.cp.arith));
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
fn eval_and_prove_direct_call(
    store: &TermStore,
    root: Hash,
    combinators: &mut ClosureCombinators<'_>,
    cap_triples: &[(i64, Anchored, Anchored)],
    arg_triples: &[(i64, Anchored, Anchored)],
) -> Option<(i64, Expr, Expr)> {
    let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
    let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
    let n = root_captures.len();

    // The computation-rule axiom for `root` -- its own first use for this
    // `Hash` may lazily push (and, transitively, prime `call_ref`/
    // `mk_env_ref` for this exact shape too), so fetched before anything
    // above is combined into a larger term.
    let axiom = combinators.call_eq_ref(root)?;
    let axiom = Anchored::new(&combinators.cp.arith, axiom);

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
        let cd: Vec<Expr> = cap_triples.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)).collect();
        let lit_c: Vec<Expr> = cap_triples
            .iter()
            .map(|&(x, _, _)| {
                combinators.cp.arith.lit(x);
                combinators.cp.arith.lit_ref(x)
            })
            .collect();
        let cp: Vec<Expr> = cap_triples.iter().map(|(_, _, p)| p.at(&combinators.cp.arith)).collect();
        let env_eq = kernel::cong_n(&int_ty, &env_ty_expr, &mk_env_expr, &cd, &lit_c, cp);
        let denoted_env = apply_n(mk_env_expr.clone(), cd);
        let lit_env = apply_n(mk_env_expr, lit_c);
        Some((denoted_env, lit_env, env_eq, env_ty_expr))
    } else {
        None
    };

    let call_fn = combinators.call_ref(root, &root_captures, &[])?; // cache hit -- primed by call_eq_ref above
    let d_args: Vec<Expr> = arg_triples.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)).collect();
    let lit_args: Vec<Expr> = arg_triples
        .iter()
        .map(|&(x, _, _)| {
            combinators.cp.arith.lit(x);
            combinators.cp.arith.lit_ref(x)
        })
        .collect();
    let p_args: Vec<Expr> = arg_triples.iter().map(|(_, _, p)| p.at(&combinators.cp.arith)).collect();

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
    let axiom_at_literals = apply_n(axiom.at(&combinators.cp.arith), axiom_args);

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
        inner_params.push(Anchored::new(&combinators.cp.arith, l.clone()));
        inner_concrete.push(x);
        inner_facts.push(Anchored::new(&combinators.cp.arith, kernel::refl(l)));
    }
    if let Some(&max_rel) = root_captures.iter().max() {
        let pad_len = root_arity + max_rel as usize + 1;
        let (fx0, _, _) = cap_triples[0];
        combinators.cp.arith.lit(fx0);
        let filler = combinators.cp.arith.lit_ref(fx0);
        while inner_params.len() < pad_len {
            inner_concrete.push(fx0);
            inner_params.push(Anchored::new(&combinators.cp.arith, filler.clone()));
            inner_facts.push(Anchored::new(&combinators.cp.arith, kernel::refl(filler.clone())));
        }
        for (j, &rel) in root_captures.iter().enumerate() {
            let (cx, _, _) = cap_triples[j];
            combinators.cp.arith.lit(cx);
            let l = combinators.cp.arith.lit_ref(cx);
            let idx = root_arity + rel as usize;
            inner_concrete[idx] = cx;
            inner_params[idx] = Anchored::new(&combinators.cp.arith, l.clone());
            inner_facts[idx] = Anchored::new(&combinators.cp.arith, kernel::refl(l));
        }
    }
    // `eval_and_prove`'s own recursion below (over `root_body`) may lazily
    // push further postulates (`assume_prim_fact`/`assume_ite_fact`,
    // fresh literals), shifting the ambient depth -- so everything built
    // above (still at the pre-recursion depth) is anchored here and
    // re-resolved fresh, via `.at()`, only once nothing more is left to
    // push, mirroring `build_ev_witness`'s own documented discipline.
    let call_at_denoted = Anchored::new(&combinators.cp.arith, call_at_denoted);
    let call_at_lit_env_lit_args = Anchored::new(&combinators.cp.arith, call_at_lit_env_lit_args);
    let bridge = Anchored::new(&combinators.cp.arith, bridge);
    let axiom_at_literals = Anchored::new(&combinators.cp.arith, axiom_at_literals);

    let (result, denote_lit, proof_d) = eval_and_prove(store, root_body, combinators, &inner_params, &inner_concrete, &inner_facts)?;

    // Chain: call_at_denoted = call_at_lit_env_lit_args (bridge)
    //      = denote(root_body, [lit_args, lit_caps]) (axiom_at_literals)
    //      = lit_ref(result) (proof_d)
    let int_ty2 = combinators.cp.arith.int_ty();
    let result_ref = combinators.cp.arith.lit_ref(result);
    let call_at_denoted = call_at_denoted.at(&combinators.cp.arith);
    let call_at_lit_env_lit_args = call_at_lit_env_lit_args.at(&combinators.cp.arith);
    let bridge = bridge.at(&combinators.cp.arith);
    let axiom_at_literals = axiom_at_literals.at(&combinators.cp.arith);
    let bridge_to_denote =
        kernel::trans_proof(&int_ty2, &call_at_denoted, &call_at_lit_env_lit_args, &denote_lit, bridge, axiom_at_literals);
    let final_proof = kernel::trans_proof(&int_ty2, &call_at_denoted, &denote_lit, &result_ref, bridge_to_denote, proof_d);
    debug_assert_has_type(
        &combinators.cp.arith.p.ctx,
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
/// captures resolved to `(i64, Anchored, Anchored)` triples, ready for
/// `eval_and_prove_direct_call` once a value is actually *called* (not
/// merely *created*) -- whichever branch the `If` concretely selects.
/// `None` if `inner` is itself self-recursive (not expected to arise here
/// -- `clo_eq_ref`'s own classification already requires a bare
/// `Term::Abs`, never `Term::Rec` -- but checked rather than assumed).
/// A concrete `(value, denoted, proof)` triple per resolved argument or
/// capture -- shared alias for the `Vec` of these `eval_and_prove_call`'s
/// own family of functions passes around, just to keep the type simple
/// enough for `clippy::type_complexity` not to flag it.
type ValueTriples = Vec<(i64, Anchored, Anchored)>;

/// `build_clo_call_bridge`'s own return: `(call_at_denoted,
/// call_at_lit_env_lit_args, bridge, axiom_at_literals, inner_params,
/// inner_concrete, inner_facts, k, shape)` -- see its own docs. A type
/// alias purely to keep this under `clippy::type_complexity`'s own
/// threshold, same rationale as `ValueTriples`.
type CloCallBridge = (Expr, Expr, Expr, Expr, Vec<Anchored>, Vec<i64>, Vec<Anchored>, usize, ClosureRhsShape);

fn inner_closure_literal_value(
    combinators: &mut ClosureCombinators<'_>,
    inner: Hash,
    inner_params: &[Anchored],
    inner_concrete: &[i64],
    inner_facts: &[Anchored],
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
        let d = Anchored::new(&combinators.cp.arith, inner_params.get(rel)?.at(&combinators.cp.arith));
        let p = Anchored::new(&combinators.cp.arith, inner_facts.get(rel)?.at(&combinators.cp.arith));
        cap_triples.push((x, d, p));
    }
    let inner_dummy: Vec<Option<usize>> = vec![None; inner_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let sym = combinators.register(inner, &inner_captures, &inner_dummy)?; // cache hit -- primed by clo_eq_ref
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
        let mk_env_expr = combinators.cp.mk_env_ref(&inner_sig); // cache hit -- primed by clo_eq_ref
        kernel::app(sym, apply_n(mk_env_expr, lit_c))
    };
    Some((value, cap_triples))
}

/// `eval_and_prove`'s own `AppShape::LitLambdaOver` case: a self-call
/// argument (or leaf expression) that over-applies a literal lambda
/// `root` -- `root`'s own saturated call (its first `root_arity`
/// arguments) returns a `Clo_k`, and the *extra* `k` arguments are then
/// dispatched against that closure via `apply_ref`. See `clo_eq_ref`'s
/// own docs for why this needs a second computation-rule axiom (root's
/// saturated call is just as opaque, `Clo`-typed, as a `call_eq_ref`-
/// covered `Int`-typed one), `ite_clo_eq_ref`'s own docs for the branch-
/// selection bridge an `If`-shaped body needs, and `apply_clo_eq_ref`'s
/// own docs for tying `apply_ref` to whichever closure value is
/// concretely produced.
///
/// Guarded by `combinator_return_type(root) == Some(Some(k))` and
/// `args.len() == root_arity + k` (the whole thing fully resolves to
/// `Int` -- matches `denote_with_placeholders`'s own identical
/// requirement, enforced there via `apply_ref`'s own `Clo_k`-typed
/// domain) -- `None` otherwise, not an error: a partial or chained
/// over-application, or one whose own saturated call stays `Int`
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
fn build_clo_call_bridge(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    subject: Hash,
    sat_arg_triples: &[(i64, Anchored, Anchored)],
    outer_params: &[Anchored],
    outer_concrete: &[i64],
    outer_facts: &[Anchored],
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
        let d = Anchored::new(&combinators.cp.arith, outer_params.get(rel)?.at(&combinators.cp.arith));
        let p = Anchored::new(&combinators.cp.arith, outer_facts.get(rel)?.at(&combinators.cp.arith));
        cap_triples.push((x, d, p));
    }
    let n = subject_captures.len();

    // The `Clo_k`-typed computation-rule axiom for `subject`'s own
    // saturated call -- its own first use for this `Hash` may lazily push
    // (and transitively prime `call_ref`/`mk_env_ref`/`register`/
    // `ite_clo_ref` for this exact shape too, see its own docs), so
    // fetched before anything above is combined into a larger term.
    let (axiom, shape) = combinators.clo_eq_ref(subject)?;
    let axiom = Anchored::new(&combinators.cp.arith, axiom);

    let sig: Vec<Option<usize>> = vec![None; n];

    // Congruence bridge over `call_ref(subject)`'s own arguments --
    // identical construction to `eval_and_prove_direct_call`'s own (see
    // its docs), generalized to the `Clo_k` codomain here instead of
    // `Int`. `int_ty`/`clo_ty` are re-derived fresh (not held across the
    // block) precisely because `.lit(x)` calls interleaved below (for any
    // capture/arg not already interned) may lazily push, which would
    // otherwise silently invalidate an earlier `Postulates::get`-derived
    // reference the same way any other unanchored value would
    // (`Anchored`'s own docs) -- this function's own recomputation is
    // cheap (a cache hit after first use), so it's simpler and safer than
    // juggling `Anchored` for these two alone; each call site below gets
    // its own fresh copy.
    let env_bridge = if n > 0 {
        let mk_env_expr = combinators.cp.mk_env_ref(&sig);
        let env_ty_expr = combinators.cp.env_ty(&sig);
        let cd: Vec<Expr> = cap_triples.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)).collect();
        let lit_c: Vec<Expr> = cap_triples
            .iter()
            .map(|&(x, _, _)| {
                combinators.cp.arith.lit(x);
                combinators.cp.arith.lit_ref(x)
            })
            .collect();
        let cp: Vec<Expr> = cap_triples.iter().map(|(_, _, p)| p.at(&combinators.cp.arith)).collect();
        let int_ty = combinators.cp.arith.int_ty();
        let env_eq = kernel::cong_n(&int_ty, &env_ty_expr, &mk_env_expr, &cd, &lit_c, cp);
        let denoted_env = apply_n(mk_env_expr.clone(), cd);
        let lit_env = apply_n(mk_env_expr, lit_c);
        Some((denoted_env, lit_env, env_eq, env_ty_expr))
    } else {
        None
    };

    let call_fn = combinators.call_ref(subject, &subject_captures, &[])?; // cache hit -- primed by clo_eq_ref above
    let d_sat_args: Vec<Expr> = sat_arg_triples.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)).collect();
    let lit_sat_args: Vec<Expr> = sat_arg_triples
        .iter()
        .map(|&(x, _, _)| {
            combinators.cp.arith.lit(x);
            combinators.cp.arith.lit_ref(x)
        })
        .collect();
    let p_sat_args: Vec<Expr> = sat_arg_triples.iter().map(|(_, _, p)| p.at(&combinators.cp.arith)).collect();

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
    let axiom_at_literals = apply_n(axiom.at(&combinators.cp.arith), axiom_args);

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
        inner_params.push(Anchored::new(&combinators.cp.arith, l.clone()));
        inner_concrete.push(x);
        inner_facts.push(Anchored::new(&combinators.cp.arith, kernel::refl(l)));
    }
    if let Some(&max_rel) = subject_captures.iter().max() {
        let pad_len = subject_arity + max_rel as usize + 1;
        let (fx0, _, _) = cap_triples[0];
        combinators.cp.arith.lit(fx0);
        let filler = combinators.cp.arith.lit_ref(fx0);
        while inner_params.len() < pad_len {
            inner_concrete.push(fx0);
            inner_params.push(Anchored::new(&combinators.cp.arith, filler.clone()));
            inner_facts.push(Anchored::new(&combinators.cp.arith, kernel::refl(filler.clone())));
        }
        for (j, &rel) in subject_captures.iter().enumerate() {
            let (cx, _, _) = cap_triples[j];
            combinators.cp.arith.lit(cx);
            let l = combinators.cp.arith.lit_ref(cx);
            let idx = subject_arity + rel as usize;
            inner_concrete[idx] = cx;
            inner_params[idx] = Anchored::new(&combinators.cp.arith, l.clone());
            inner_facts[idx] = Anchored::new(&combinators.cp.arith, kernel::refl(l));
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
/// through (there is only ever one `apply_ref(k)` step in the whole
/// chain, applied once `chosen` is finally reached), so every recursive
/// call threads the same ones through unchanged.
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
/// bridging `apply_ref(k)` applied to `chosen_value` down to a direct
/// call on `chosen`.
#[allow(clippy::too_many_arguments)]
fn resolve_closure_shape_to_leaf(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    call_at_denoted: &Expr,
    call_at_lit_env_lit_args: &Expr,
    bridge: &Expr,
    axiom_at_literals: &Expr,
    shape: &ClosureRhsShape,
    inner_params: &[Anchored],
    inner_concrete: &[i64],
    inner_facts: &[Anchored],
    k: usize,
    extra_arg_triples: &[(i64, Anchored, Anchored)],
) -> Option<(Hash, ValueTriples, ValueTriples, Expr, Expr, Expr)> {
    let call_at_denoted = Anchored::new(&combinators.cp.arith, call_at_denoted.clone());
    let call_at_lit_env_lit_args = Anchored::new(&combinators.cp.arith, call_at_lit_env_lit_args.clone());
    let bridge = Anchored::new(&combinators.cp.arith, bridge.clone());
    let axiom_at_literals = Anchored::new(&combinators.cp.arith, axiom_at_literals.clone());

    match shape {
        ClosureRhsShape::IfTree(tree) => {
            let leaf_shapes = classify_closure_if_tree_leaves(store, tree, k)?;
            let (chosen, chosen_cap_triples, chosen_arg_prefix, tree_value_at_literals, chosen_value_lit, tree_to_chosen) =
                resolve_closure_if_tree(store, combinators, tree, &leaf_shapes, inner_params, inner_concrete, inner_facts, k)?;
            let tree_value_at_literals = Anchored::new(&combinators.cp.arith, tree_value_at_literals);
            let chosen_value_lit = Anchored::new(&combinators.cp.arith, chosen_value_lit);
            let tree_to_chosen = Anchored::new(&combinators.cp.arith, tree_to_chosen);

            // Nothing pushes past here -- resolve everything fresh, in one
            // batch, only once nothing more is left to push.
            let call_at_denoted_here = call_at_denoted.at(&combinators.cp.arith);
            let call_at_lit_env_lit_args_here = call_at_lit_env_lit_args.at(&combinators.cp.arith);
            let bridge_here = bridge.at(&combinators.cp.arith);
            let axiom_at_literals_here = axiom_at_literals.at(&combinators.cp.arith);
            let tree_value_at_literals = tree_value_at_literals.at(&combinators.cp.arith);
            let chosen_value_lit = chosen_value_lit.at(&combinators.cp.arith);
            let tree_to_chosen = tree_to_chosen.at(&combinators.cp.arith);
            let clo_ty = combinators.cp.clo_ty(k); // cache hit -- primed by clo_eq_ref via clo_ty(k)

            // `axiom_at_literals`'s own RHS is exactly the tree's own
            // formula at literals (`tree_value_at_literals`, independently
            // reconstructed here the same way `resolve_closure_if_tree`'s
            // own recursive descent builds it) -- bridge `subject`'s call
            // to that formula, then to the concretely-reached leaf's own
            // value, via `tree_to_chosen` (one `ite_clo_eq_ref` step per
            // internal node on the path actually taken).
            let root_to_tree_value =
                kernel::trans_proof(&clo_ty, &call_at_denoted_here, &call_at_lit_env_lit_args_here, &tree_value_at_literals, bridge_here, axiom_at_literals_here);
            let root_to_chosen = kernel::trans_proof(&clo_ty, &call_at_denoted_here, &tree_value_at_literals, &chosen_value_lit, root_to_tree_value, tree_to_chosen);

            // `apply_clo_eq_ref(chosen)` (a bare `Abs`-shaped leaf, exactly
            // `k`-ary already) or `apply_pap_eq_ref(chosen, s)` (a
            // `Pap`-shaped leaf, `chosen` there being `g`, whose own
            // arity is `s + k`) -- `chosen_arg_prefix` is empty for the
            // former and non-empty for the latter (a `Pap`-shaped leaf's
            // own classification requires at least one supplied arg, see
            // `classify_closure_if_tree_leaf`), so it doubles as the
            // dispatch signal here without threading a separate flag.
            // Either axiom's own first use for this key may lazily push,
            // so everything built above is anchored *first* (a push that
            // happens *before* wrapping a value in `Anchored` is captured
            // at the already-grown depth, silently computing a zero shift
            // later -- this ordering bug was caught here, not by
            // inspection).
            let root_to_chosen = Anchored::new(&combinators.cp.arith, root_to_chosen);
            let chosen_value_lit = Anchored::new(&combinators.cp.arith, chosen_value_lit);
            let s = chosen_arg_prefix.len();
            let apply_axiom = if s == 0 { combinators.apply_clo_eq_ref(chosen)? } else { combinators.apply_pap_eq_ref(chosen, s)? };
            let apply_axiom = Anchored::new(&combinators.cp.arith, apply_axiom);

            let root_to_chosen = root_to_chosen.at(&combinators.cp.arith);
            let chosen_value_lit = chosen_value_lit.at(&combinators.cp.arith);

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
                .chain(chosen_arg_prefix.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)))
                .chain(extra_arg_triples.iter().rev().map(|(_, d, _)| d.at(&combinators.cp.arith)))
                .collect();
            let apply_eq_chosen = apply_n(apply_axiom.at(&combinators.cp.arith), apply_axiom_args);

            let mut chosen_arg_triples = chosen_arg_prefix;
            chosen_arg_triples.extend(extra_arg_triples.iter().cloned());

            Some((chosen, chosen_cap_triples, chosen_arg_triples, chosen_value_lit, root_to_chosen, apply_eq_chosen))
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
                let d = Anchored::new(&combinators.cp.arith, inner_params.get(rel)?.at(&combinators.cp.arith));
                let p = Anchored::new(&combinators.cp.arith, inner_facts.get(rel)?.at(&combinators.cp.arith));
                g_cap_triples.push((x, d, p));
            }

            let mut supplied_triples = Vec::with_capacity(s);
            for &a in args {
                let (x, d, p) = eval_and_prove(store, a, combinators, inner_params, inner_concrete, inner_facts)?;
                supplied_triples.push((x, Anchored::new(&combinators.cp.arith, d), Anchored::new(&combinators.cp.arith, p)));
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
            let pap_fn = Anchored::new(&combinators.cp.arith, pap_fn);

            let call_at_denoted_here = call_at_denoted.at(&combinators.cp.arith);
            let call_at_lit_env_lit_args_here = call_at_lit_env_lit_args.at(&combinators.cp.arith);
            let bridge_here = bridge.at(&combinators.cp.arith);
            let axiom_at_literals_here = axiom_at_literals.at(&combinators.cp.arith);
            let pap_fn = pap_fn.at(&combinators.cp.arith);
            let clo_ty = combinators.cp.clo_ty(k); // cache hit -- primed by clo_eq_ref_pap via pap_ref

            let g_env_denoted = if g_cap_triples.is_empty() {
                None
            } else {
                let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
                let mk_env_expr = combinators.cp.mk_env_ref(&g_sig); // cache hit -- primed by clo_eq_ref_pap
                let cd: Vec<Expr> = g_cap_triples.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)).collect();
                Some(apply_n(mk_env_expr, cd))
            };
            let d_supplied: Vec<Expr> = supplied_triples.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)).collect();
            let mut pap_args = Vec::with_capacity(1 + s);
            pap_args.extend(g_env_denoted);
            pap_args.extend(d_supplied);
            let pap_at_denoted = apply_n(pap_fn, pap_args);

            let root_to_chosen =
                kernel::trans_proof(&clo_ty, &call_at_denoted_here, &call_at_lit_env_lit_args_here, &pap_at_denoted, bridge_here, axiom_at_literals_here);

            // `apply_pap_eq_ref(g, s)` -- its own first use for this
            // `(g, s)` may lazily push, so everything built above is
            // anchored *first*, same discipline `IfTree`'s own
            // `apply_clo_eq_ref` call above uses.
            let root_to_chosen = Anchored::new(&combinators.cp.arith, root_to_chosen);
            let pap_at_denoted = Anchored::new(&combinators.cp.arith, pap_at_denoted);
            let apply_axiom = combinators.apply_pap_eq_ref(g, s)?;
            let apply_axiom = Anchored::new(&combinators.cp.arith, apply_axiom);

            let root_to_chosen = root_to_chosen.at(&combinators.cp.arith);
            let pap_at_denoted = pap_at_denoted.at(&combinators.cp.arith);

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
                .chain(supplied_triples.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)))
                .chain(extra_arg_triples.iter().rev().map(|(_, d, _)| d.at(&combinators.cp.arith)))
                .collect();
            let apply_eq_chosen = apply_n(apply_axiom.at(&combinators.cp.arith), apply_axiom_args);

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
                g_arg_triples.push((x, Anchored::new(&combinators.cp.arith, d), Anchored::new(&combinators.cp.arith, p)));
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
            let call_at_denoted_here = call_at_denoted.at(&combinators.cp.arith);
            let call_at_lit_env_lit_args_here = call_at_lit_env_lit_args.at(&combinators.cp.arith);
            let bridge_here = bridge.at(&combinators.cp.arith);
            let axiom_at_literals_here = axiom_at_literals.at(&combinators.cp.arith);
            let clo_ty = combinators.cp.clo_ty(k);
            let root_to_g = kernel::trans_proof(&clo_ty, &call_at_denoted_here, &call_at_lit_env_lit_args_here, &g_call_at_denoted, bridge_here, axiom_at_literals_here);

            // The recursive `resolve_closure_shape_to_leaf` call just
            // below may lazily push a great many further postulates (its
            // own recursion could itself be another `Call`, on top of
            // whatever `g`'s own `IfTree`/`Pap` resolution needs) --
            // anchor everything built above *now*; re-resolved fresh
            // afterward (`clo_ty` too -- a `Postulates::get`-derived
            // reference is exactly as stale-prone as any other unanchored
            // value, see `build_clo_call_bridge`'s own identical
            // rationale, and reusing it unchanged here was a genuine bug
            // caught by `debug_assert_has_type` below, not by inspection)
            // only once nothing more is left to push, same discipline
            // this whole file uses throughout.
            let root_to_g = Anchored::new(&combinators.cp.arith, root_to_g);
            let g_call_at_denoted = Anchored::new(&combinators.cp.arith, g_call_at_denoted);

            let (chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, g_to_chosen, apply_eq_chosen) = resolve_closure_shape_to_leaf(
                store,
                combinators,
                &g_call_at_denoted.at(&combinators.cp.arith),
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
            let root_to_g = root_to_g.at(&combinators.cp.arith);
            let g_call_at_denoted = g_call_at_denoted.at(&combinators.cp.arith);
            let call_at_denoted = call_at_denoted.at(&combinators.cp.arith);
            let root_to_chosen = kernel::trans_proof(&clo_ty, &call_at_denoted, &g_call_at_denoted, &chosen_value, root_to_g, g_to_chosen);
            debug_assert_has_type(
                &combinators.cp.arith.p.ctx,
                &root_to_chosen,
                &kernel::id(clo_ty, call_at_denoted, chosen_value.clone()),
                "resolve_closure_shape_to_leaf: Call arm's own root_to_chosen",
            );

            Some((chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, root_to_chosen, apply_eq_chosen))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn eval_and_prove_call_over(
    store: &TermStore,
    root: Hash,
    args: &[Hash],
    callee_param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[Anchored],
    concrete: &[i64],
    param_facts: &[Anchored],
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
        arg_triples.push((x, Anchored::new(&combinators.cp.arith, d), Anchored::new(&combinators.cp.arith, p)));
    }
    let (sat_arg_triples, extra_arg_triples) = arg_triples.split_at(root_arity);

    let (call_at_denoted, call_at_lit_env_lit_args, bridge, axiom_at_literals, inner_params, inner_concrete, inner_facts, k, shape) =
        build_clo_call_bridge(store, combinators, root, sat_arg_triples, params, concrete, param_facts)?;
    debug_assert_eq!(k, k_check, "eval_and_prove_call_over: build_clo_call_bridge's own k must match combinator_return_type(root)");

    // `resolve_closure_shape_to_leaf` below may lazily push further
    // postulates (its own recursion into a `Call`'s own `g`, priming
    // `apply_clo_eq_ref`/`apply_pap_eq_ref`, ...) -- anchor `call_at_denoted`
    // now so it can be re-resolved fresh afterward, in the shared tail;
    // the other three are consumed (cloned) immediately inside that call,
    // so they don't need to survive past it.
    let call_at_denoted = Anchored::new(&combinators.cp.arith, call_at_denoted);

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
    // `apply_*_eq_ref` fact bridging `apply_ref(k)` applied to
    // `chosen_value` down to a direct call on `chosen`.
    let (chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, root_to_chosen, apply_eq_chosen) = resolve_closure_shape_to_leaf(
        store,
        combinators,
        &call_at_denoted.at(&combinators.cp.arith),
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

    let apply_fn = combinators.cp.apply_ref(k); // cache hit -- primed by apply_clo_eq_ref/apply_pap_eq_ref above
    let call_at_denoted = call_at_denoted.at(&combinators.cp.arith);
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
    // literals first" step for `apply_ref`'s own `k` `Int` arguments is
    // needed at all.
    let d_extra_args: Vec<Expr> = extra_arg_triples.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)).collect();

    // `cong1` over `apply_ref(k)`'s own first (`Clo_k`) argument, the `k`
    // extra args held fixed at their denoted values, using
    // `root_to_chosen` to turn `call_at_denoted` into `chosen_value`.
    let mut f_clo_body = kernel::app(kernel::shift(&apply_fn, 0, 1), kernel::var(0));
    for d in &d_extra_args {
        f_clo_body = kernel::app(f_clo_body, kernel::shift(d, 0, 1));
    }
    let f_clo = kernel::lam(clo_ty.clone(), f_clo_body);
    let clo_step = kernel::cong1(&clo_ty, &int_ty2, &f_clo, call_at_denoted.clone(), chosen_value.clone(), root_to_chosen);
    let apply_at_denoted = apply_n(apply_fn.clone(), std::iter::once(call_at_denoted).chain(d_extra_args.iter().cloned()));
    let apply_at_chosen_denoted_args = apply_n(apply_fn, std::iter::once(chosen_value).chain(d_extra_args.iter().cloned()));

    // `eval_and_prove_direct_call`'s own recursion below (into `chosen`'s
    // own body) may lazily push further postulates -- anchor everything
    // built above now, re-resolved fresh only once nothing more is left
    // to push, same discipline `eval_and_prove_direct_call` itself uses.
    let apply_at_denoted = Anchored::new(&combinators.cp.arith, apply_at_denoted);
    let apply_at_chosen_denoted_args = Anchored::new(&combinators.cp.arith, apply_at_chosen_denoted_args);
    let clo_step = Anchored::new(&combinators.cp.arith, clo_step);
    let apply_eq_chosen = Anchored::new(&combinators.cp.arith, apply_eq_chosen);

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
    let apply_at_denoted = apply_at_denoted.at(&combinators.cp.arith);
    let apply_at_chosen_denoted_args = apply_at_chosen_denoted_args.at(&combinators.cp.arith);
    let clo_step = clo_step.at(&combinators.cp.arith);
    let apply_eq_chosen = apply_eq_chosen.at(&combinators.cp.arith);
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
        &combinators.cp.arith.p.ctx,
        &final_proof,
        &kernel::id(int_ty3, apply_at_denoted.clone(), result_ref),
        "eval_and_prove_call_over: final proof",
    );
    Some((result, apply_at_denoted, final_proof))
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
    combinators: &mut ClosureCombinators<'_>,
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
        return Some((v.at(&combinators.cp.arith), e.at(&combinators.cp.arith)));
    }
    *budget = budget.checked_sub(1)?;

    let leaf_idx = leaves
        .iter()
        .position(|leaf| leaf.path.iter().all(|&(cond, lit)| eval_concrete(store, cond, concrete) == Some(lit)))?;
    let leaf = &leaves[leaf_idx];

    // Canonical params for this level: literals, trivially equal to
    // themselves -- see the section docs above for why this (not a
    // caller-supplied denoted expression) is what makes `memo` sound.
    let params: Vec<Anchored> =
        concrete.iter().map(|&c| Anchored::new(&combinators.cp.arith, combinators.cp.arith.lit_ref(c))).collect();
    let param_facts: Vec<Anchored> = params
        .iter()
        .map(|p| Anchored::new(&combinators.cp.arith, kernel::refl(p.at(&combinators.cp.arith))))
        .collect();

    // Collected across the loops below, which push further postulates
    // (assume_prim_fact, and every self-call's own recursion) -- anchor
    // each one immediately so it can be resolved fresh once everything is
    // done growing, at the final assembly below.
    let mut premises = Vec::with_capacity(leaf.path.len());
    for &(cond, _lit) in &leaf.path {
        let (_, _, proof) = eval_and_prove(store, cond, combinators, &params, concrete, &param_facts)?;
        premises.push(Anchored::new(&combinators.cp.arith, proof));
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
            denoted_args.push(Anchored::new(&combinators.cp.arith, denoted));
            denoted_facts.push(Anchored::new(&combinators.cp.arith, pf));
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
        let v = Anchored::new(&combinators.cp.arith, v);
        let e_canonical = Anchored::new(&combinators.cp.arith, e_canonical);

        // Recast `e_canonical : Ev(lit_params, v)` to `Ev(denoted_params,
        // v)` -- what *this* leaf's own `Ev` constructor actually expects
        // for its e_i (its type was built from the call's real argument
        // expressions, not just their values) -- via congruence over the
        // params (`cong_n`, `Ev` held fixed at `v`) and transport along the
        // resulting type equality.
        let int_ty = combinators.cp.arith.int_ty();
        let lit_params: Vec<Expr> = new_concrete.iter().map(|&x| combinators.cp.arith.lit_ref(x)).collect();
        let denoted_params: Vec<Expr> = denoted_args.iter().map(|a| a.at(&combinators.cp.arith)).collect();
        let ps: Vec<Expr> = denoted_facts
            .iter()
            .zip(&denoted_params)
            .zip(&lit_params)
            .map(|((pf, dp), lp)| kernel::sym(&int_ty, dp, lp, pf.at(&combinators.cp.arith)))
            .collect();
        let v_resolved = v.at(&combinators.cp.arith);
        let v_anchored = Anchored::new(&combinators.cp.arith, v_resolved.clone());
        let f = params_and_close(&mut combinators.cp.arith, self_call.arity, kernel::close_lam, |arith, pp| {
            Some(ev_of(arith, ev_pos, &pp.at(arith), v_anchored.at(arith)))
        })?;
        let ev_eq = kernel::cong_n(&int_ty, &kernel::sort(0), &f, &lit_params, &denoted_params, ps);
        let e = kernel::transport(
            0,
            ev_of(&combinators.cp.arith, ev_pos, &lit_params, v_resolved.clone()),
            ev_of(&combinators.cp.arith, ev_pos, &denoted_params, v_resolved),
            ev_eq,
            e_canonical.at(&combinators.cp.arith),
        );
        vs.push(v);
        es.push(Anchored::new(&combinators.cp.arith, e));
    }

    // Nothing left to grow arith.p.ctx from here -- resolve everything
    // fresh, once, for the final assembly.
    let params: Vec<Expr> = params.iter().map(|a| a.at(&combinators.cp.arith)).collect();
    let premises: Vec<Expr> = premises.iter().map(|a| a.at(&combinators.cp.arith)).collect();
    let vs: Vec<Expr> = vs.iter().map(|a| a.at(&combinators.cp.arith)).collect();
    let es: Vec<Expr> = es.iter().map(|a| a.at(&combinators.cp.arith)).collect();

    let args = params.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es);
    let e = apply_n(combinators.cp.arith.p.get(ev_leaf_positions[leaf_idx]), args);
    let v = combine_of(&combinators.cp.arith, &combines[leaf_idx], &params, &vs);
    let int_ty_check = combinators.cp.arith.int_ty();
    debug_assert_has_type(&combinators.cp.arith.p.ctx, &v, &int_ty_check, "build_ev_witness: v");
    let ev_check = ev_of(&combinators.cp.arith, ev_pos, &params, v.clone());
    debug_assert_has_type(&combinators.cp.arith.p.ctx, &e, &ev_check, "build_ev_witness: e");
    memo.insert(concrete.to_vec(), (Anchored::new(&combinators.cp.arith, v.clone()), Anchored::new(&combinators.cp.arith, e.clone())));
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

/// A cheap, `Expr`-free dry run of `build_ev_witness`'s own recursion
/// structure: walks the same leaves, resolving each `If` on the way to
/// one via plain `i64` arithmetic (`eval_concrete`, never touching a
/// kernel term), and counts how many *distinct* concrete-argument nodes
/// get visited -- deduplicating exactly the way `build_ev_witness`'s own
/// `memo` does, so a value revisited from two different call sites (as
/// naive Fibonacci's overlapping subproblems are) counts once. Returns
/// early, without finishing the walk, once `cap` distinct visits are
/// reached -- the caller only needs to know whether this crosses a small
/// threshold, not the exact count for a large instance, so this stays
/// cheap even when the real answer is large. Returns `cap` itself (not
/// panicking or guessing) if a leaf can't be found or an argument can't
/// be evaluated concretely -- `instance_from_scaffold`'s own
/// `build_ev_witness` call will discover and report that properly; this
/// only decides a performance question, never a correctness one, so it's
/// fine to be conservative (assume "expensive") on any surprise here.
fn instance_visit_count(store: &TermStore, self_call: SelfCall, leaves: &[Leaf], concrete: &[i64], cap: usize) -> usize {
    // Returns `false` once nothing more needs walking: either `cap` is
    // already reached, or a leaf/argument couldn't be resolved (treated
    // as "assume expensive" by the caller, via the early `return cap`
    // below, rather than guessing a count for a shape it doesn't
    // recognize).
    fn visit(store: &TermStore, self_call: SelfCall, leaves: &[Leaf], concrete: &[i64], seen: &mut HashSet<Vec<i64>>, cap: usize) -> bool {
        if seen.len() >= cap {
            return true;
        }
        if !seen.insert(concrete.to_vec()) {
            return false;
        }
        let Some(leaf) = leaves.iter().find(|leaf| leaf.path.iter().all(|&(cond, lit)| eval_concrete(store, cond, concrete) == Some(lit))) else {
            return true; // unrecognized shape -- conservatively "expensive"
        };
        for call in &leaf.calls {
            let mut new_concrete = Vec::with_capacity(self_call.arity);
            let mut ok = true;
            for i in 0..self_call.arity {
                let arg = call[self_call.arity - 1 - i];
                match eval_concrete(store, arg, concrete) {
                    Some(x) => new_concrete.push(x),
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                return true; // couldn't evaluate an argument concretely -- conservatively "expensive"
            }
            if visit(store, self_call, leaves, &new_concrete, seen, cap) {
                return true;
            }
        }
        false
    }
    let mut seen = HashSet::new();
    if visit(store, self_call, leaves, concrete, &mut seen, cap) {
        return cap;
    }
    seen.len()
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

    // Automatically wrapped in `kernel::with_shift_cache` exactly when
    // *this concrete instance* actually revisits enough distinct memoized
    // nodes to matter -- not just when the function's own shape has a
    // branching leaf. An earlier version of this gated on shape alone
    // (any leaf with more than one self-call) and regressed `jit.rs`'s
    // own routine sample verification for a branching-shaped function
    // like `fib`: `sample_arg_vectors`'s own small samples (0, 1, 2, ...)
    // still trigger only a handful of `build_ev_witness` nodes even for a
    // branching shape, so shape alone can't distinguish that from the
    // large instance the cache is actually for (confirmed by the
    // `fib(30)` demo's cold-compile time regressing when shape alone was
    // used to decide). `instance_visit_count` is a cheap, *exact* dry run
    // of `build_ev_witness`'s own memoized recursion structure, using
    // only plain `i64` arithmetic (no `Expr`/postulate construction at
    // all) -- not a fuzzy prediction, since it walks the very same leaves
    // and `memo`-style dedup `build_ev_witness` itself will use, just
    // without building any proof term. `VISIT_THRESHOLD` is picked from
    // the actual samples this matters for: `fib(8)` (this cache's own
    // proven ~2x win, `fibonacci_branching_leaves_get_kernel_checked_instances`)
    // visits 9 distinct nodes; `jit.rs`'s own routine samples up to `n=3`
    // visit at most 4.
    const VISIT_THRESHOLD: usize = 6;
    let use_shift_cache = instance_visit_count(store, scaffold.self_call, &scaffold.leaves, &concrete, VISIT_THRESHOLD) >= VISIT_THRESHOLD;

    let build = move || -> Option<UniversalInstanceProof> {
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
    };
    if use_shift_cache {
        kernel::with_shift_cache(build)
    } else {
        build()
    }
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
/// a caller's own `combinators` is always safe -- nothing here can go
/// stale the way a lazy postulate push could (see `Anchored`'s own docs).
enum AppShape {
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

fn classify_app_node(store: &TermStore, h: Hash, param_types: &[Option<usize>]) -> Option<AppShape> {
    if !matches!(store.resolve(h), Term::App(..)) {
        return None;
    }
    let (root, args) = compile::unwind_app_spine(store, h);
    match store.resolve(root) {
        Term::Var(i) => {
            let k = (*param_types.get(*i as usize)?)?;
            (args.len() == k).then_some(AppShape::ParamCall { root, k, args })
        }
        Term::Abs(_) | Term::Rec(_) => {
            let callee_param_types = param_types_for(store, root)?;
            let arity = callee_param_types.len();
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
    apply_pos: HashMap<usize, usize>,
    combinator_value_pos: HashMap<Hash, usize>,
    combinator_call_pos: HashMap<Hash, usize>,
    env_ty_pos: HashMap<Vec<Option<usize>>, usize>,
    mk_env_pos: HashMap<Vec<Option<usize>>, usize>,
    mk_clo_pos: HashMap<Hash, usize>,
    pap_pos: HashMap<(Hash, usize), usize>,
    ite_clo_pos: HashMap<usize, usize>,
    /// `call_eq_ref`'s own memoization -- see its docs.
    call_eq_pos: HashMap<Hash, usize>,
    /// `clo_eq_ref`'s own memoization -- see its docs. Keeps the matched
    /// `ClosureRhsShape` alongside the axiom's own position so a memo hit
    /// doesn't need to re-classify `h`'s own body.
    clo_eq_pos: HashMap<Hash, (usize, ClosureRhsShape)>,
    /// `ite_clo_eq_ref`'s own memoization -- see its docs. Keyed by the
    /// concrete condition value, not a collapsed boolean (see its docs).
    ite_clo_eq_pos: HashMap<(i64, usize), usize>,
    /// `apply_clo_eq_ref`'s own memoization -- see its docs.
    apply_clo_eq_pos: HashMap<Hash, usize>,
    /// `apply_pap_eq_ref`'s own memoization -- see its docs.
    apply_pap_eq_pos: HashMap<(Hash, usize), usize>,
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
            apply_pos: HashMap::new(),
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
    /// `Int` result" (`apply_ref`'s own arguments/result are uniformly
    /// `Int` regardless of what the callee's own body does with them,
    /// matching `compile.rs`'s own untyped `call_indirect` dispatch), and a
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
    /// re-resolve-after-push dance) -- but keeps `&mut self` and keeps
    /// eagerly priming `ite_clo_ref(arity)`'s own postulate as a side
    /// effect, exactly as before: every existing call site below was
    /// written assuming `clo_ty(k)` leaves `ite_clo_ref(k)` primed
    /// afterward, and `ite_clo_ref` itself is still a genuine postulate
    /// (see its own docs for why it isn't derivable the way `Clo_arity`
    /// itself now is).
    fn clo_ty(&mut self, arity: usize) -> Expr {
        self.ite_clo_ref(arity); // side effect only -- see this function's own doc
        self.curried_int_ty(arity)
    }

    /// The literal `Int -> .. -> Int` (`arity` copies) type on its own,
    /// with no side effect -- `clo_ty`'s own pure core, factored out so
    /// `ite_clo_ref` can use this same shape for its own domain/codomain
    /// without calling back into `clo_ty` itself (which would re-trigger
    /// `clo_ty`'s own `ite_clo_ref`-priming side effect and recurse
    /// forever on `ite_clo_ref`'s first call for a given arity).
    fn curried_int_ty(&self, arity: usize) -> Expr {
        let int_ty = self.arith.int_ty();
        let mut ty = int_ty.clone();
        for _ in 0..arity {
            ty = kernel::arrow(int_ty.clone(), ty);
        }
        ty
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
    /// branches (and the result) differ. Genuinely opaque and not
    /// derivable, unlike `Clo_arity` itself: its condition is `Int`, and
    /// `Int` has no recursor in this kernel (deliberately -- it's an
    /// open-ended arithmetic domain, grounded only per concrete value, see
    /// `ArithPostulates::assume_prim_fact`/`assume_ite_fact`, never given a
    /// case-elimination principle), so there's no way to build this from
    /// anything already postulated (see `RELATED_WORK.md` section 11's own
    /// correction). Called as a side effect from every `clo_ty(arity)`
    /// call (see its own docs) as well as directly wherever only the
    /// priming, not the `Clo_arity` value itself, is needed.
    fn ite_clo_ref(&mut self, arity: usize) -> Expr {
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
    fn call_eq_ref(&mut self, h: Hash) -> Option<Expr> {
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

        // Prime `call_ref` for this exact shape first (which itself primes
        // `mk_env_ref`/`clo_ty` etc. as needed) -- may lazily push, and the
        // quantified construction below needs a stable base depth to build
        // from.
        let call_fn = self.call_ref(h, &captures, &dummy_caller_param_types)?;
        let call_fn = Anchored::new(&self.cp.arith, call_fn);

        // Quantify `n_captures + arity` fresh `Int` postulates -- captures
        // first, then `h`'s own params, an arbitrary but fixed order (only
        // the *values* pulled out of `pp` below need to match this).
        let quant_types = vec![None; n_captures + arity];
        let store = self.store;
        let ty = params_and_close_typed(self, &quant_types, kernel::close_pi, |combinators, pp| {
            let all = pp.at(&combinators.cp.arith);
            let (cs, ps) = all.split_at(n_captures);
            let call_fn_here = call_fn.at(&combinators.cp.arith);

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
    /// *extra* arguments are dispatched against it via `apply_ref`) to get
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
    fn clo_eq_ref(&mut self, root: Hash) -> Option<(Expr, ClosureRhsShape)> {
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
    /// one, `mk_env_ref` for any leaf that captures, `clo_ty(k)`/
    /// `ite_clo_ref(k)` for the `If` shape) is
    /// primed *before* `params_and_close_typed` pushes `root`'s own
    /// quantified captures/params below, not lazily from inside that
    /// closure: `params_and_close_typed`'s own `close_pi` call wraps
    /// *every* position pushed onto `arith.p.ctx` between its own base
    /// depth and wherever the closure leaves it as a Pi binder, not just
    /// the ones the closure itself asked for -- a lazy push from *inside*
    /// the closure would silently become a spurious, unused extra `Pi`
    /// argument in this axiom's own type (unlike `call_eq_ref`, whose own
    /// `mk_env_ref` call inside its closure is, in every actual caller,
    /// already primed by the time it runs -- `eval_and_prove` is only
    /// ever reached from `instance_from_scaffold`, which always builds
    /// the closure-aware universal proof first, over the same
    /// `combinators`, and that pass's own `denote_with_placeholders`
    /// already primes `mk_env_ref` for `root`'s own capture signature;
    /// `root`'s own body, though, is never *entered* by that pass at all
    /// -- `ClosureCombinators`'s own docs: "a combinator's body is never
    /// denoted here... registering one never discovers more work" -- so
    /// nothing upstream of this axiom ever primes any leaf's own
    /// postulates ahead of time the way it does for `root`'s own).
    fn clo_eq_ref_if_tree(&mut self, root: Hash, arity: usize, body: Hash, is_rec: bool, k: usize) -> Option<(Expr, ClosureRhsShape)> {
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

        // Prime `call_ref`/`mk_env_ref` for `root`'s own shape (mirrors
        // `call_eq_ref`'s identical priming), `register`/`mk_env_ref` for
        // every leaf's own shape, and `clo_ty(k)` (which also eagerly
        // primes `ite_clo_ref(k)`) -- see this method's own docs for why
        // this must all happen *before* `params_and_close_typed` below,
        // not lazily inside its closure.
        let call_fn = self.call_ref(root, &captures, &dummy_caller_param_types)?;
        let call_fn = Anchored::new(&self.cp.arith, call_fn);
        if n_captures > 0 {
            self.cp.mk_env_ref(&sig);
        }
        prime_closure_if_tree_leaves(self, &leaf_shapes)?;
        self.cp.clo_ty(k); // also primes ite_clo_ref(k), see its own docs

        // Quantify `n_captures + arity` fresh `Int` postulates -- same
        // order (captures first, then `root`'s own params) `call_eq_ref`
        // itself uses.
        let quant_types = vec![None; n_captures + arity];
        let store = self.store;
        let ty = params_and_close_typed(self, &quant_types, kernel::close_pi, |combinators, pp| {
            let all = pp.at(&combinators.cp.arith);
            let (cs, ps) = all.split_at(n_captures);
            let call_fn_here = call_fn.at(&combinators.cp.arith);

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

            let clo_ty = combinators.cp.clo_ty(k); // cache hit -- primed above
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
    /// Same priming discipline as `clo_eq_ref_if_tree`'s own docs
    /// describe: `call_ref`/`mk_env_ref` for `root`'s own shape, `g`'s own
    /// `call_ref`/`mk_env_ref` too (needed directly in the RHS below,
    /// *not* `g`'s own `clo_eq_ref` axiom -- see above), all primed before
    /// `params_and_close_typed` pushes `root`'s own quantified
    /// captures/params, not lazily from inside that closure.
    fn clo_eq_ref_call(&mut self, root: Hash, arity: usize, body: Hash, is_rec: bool, k: usize) -> Option<(Expr, ClosureRhsShape)> {
        let (g, args) = compile::unwind_app_spine(self.store, body);
        if !matches!(self.store.resolve(g), Term::Abs(_) | Term::Rec(_)) {
            return None;
        }
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

        // Prime `call_ref`/`mk_env_ref` for `root`'s own shape, then `g`'s
        // own -- see this method's own docs for why this must happen
        // before `params_and_close_typed` below.
        let call_fn = self.call_ref(root, &captures, &dummy_caller_param_types)?;
        let call_fn = Anchored::new(&self.cp.arith, call_fn);
        if n_captures > 0 {
            self.cp.mk_env_ref(&sig);
        }
        let (g_arity2, g_body, g_is_rec) = compile::peel(self.store, g)?;
        let g_captures = compile::free_vars(self.store, g_body, g_arity2, g_is_rec);
        let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let g_call_fn = self.call_ref(g, &g_captures, &g_dummy)?;
        let g_call_fn = Anchored::new(&self.cp.arith, g_call_fn);
        if !g_captures.is_empty() {
            let g_sig = capture_sig(&g_captures, &g_dummy)?;
            self.cp.mk_env_ref(&g_sig);
        }

        // Quantify `n_captures + arity` fresh `Int` postulates -- same
        // order `clo_eq_ref_pap`/`call_eq_ref` both use.
        let quant_types = vec![None; n_captures + arity];
        let store = self.store;
        let ty = params_and_close_typed(self, &quant_types, kernel::close_pi, |combinators, pp| {
            let all = pp.at(&combinators.cp.arith);
            let (cs, ps) = all.split_at(n_captures);
            let call_fn_here = call_fn.at(&combinators.cp.arith);

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
            let g_call_fn_here = g_call_fn.at(&combinators.cp.arith);
            let g_env = if g_captures.is_empty() {
                None
            } else {
                let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
                let mk_env_expr = combinators.cp.mk_env_ref(&g_sig); // cache hit -- primed above
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

            let clo_ty = combinators.cp.clo_ty(k); // cache hit -- primed by call_ref(g) above
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
    /// Same priming discipline as `clo_eq_ref_if_tree`'s own docs
    /// describe: `call_ref`/`mk_env_ref` for `root`'s own shape,
    /// `pap_ref`/`mk_env_ref` for `g`'s, all primed before
    /// `params_and_close_typed` pushes `root`'s own quantified
    /// captures/params, not lazily from inside that closure.
    fn clo_eq_ref_pap(&mut self, root: Hash, arity: usize, body: Hash, is_rec: bool, _param_types: &[Option<usize>], k: usize) -> Option<(Expr, ClosureRhsShape)> {
        let (g, args) = compile::unwind_app_spine(self.store, body);
        if !matches!(self.store.resolve(g), Term::Abs(_) | Term::Rec(_)) {
            return None;
        }
        let g_param_types = param_types_for(self.store, g)?;
        if g_param_types.iter().any(Option::is_some) {
            return None;
        }
        let g_arity = g_param_types.len();
        if args.len() >= g_arity || g_arity - args.len() != k {
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

        // Prime `call_ref`/`mk_env_ref` for `root`'s own shape, `pap_ref`/
        // `mk_env_ref` for `g`'s -- see this method's own docs for why
        // this must happen before `params_and_close_typed` below.
        let call_fn = self.call_ref(root, &captures, &dummy_caller_param_types)?;
        let call_fn = Anchored::new(&self.cp.arith, call_fn);
        if n_captures > 0 {
            self.cp.mk_env_ref(&sig);
        }
        let (_, g_body, g_is_rec) = compile::peel(self.store, g)?;
        let g_captures = compile::free_vars(self.store, g_body, g_arity, g_is_rec);
        let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let pap_fn = self.pap_ref(g, args.len(), &g_dummy)?;
        let pap_fn = Anchored::new(&self.cp.arith, pap_fn);
        if !g_captures.is_empty() {
            let g_sig = capture_sig(&g_captures, &g_dummy)?;
            self.cp.mk_env_ref(&g_sig);
        }

        // Quantify `n_captures + arity` fresh `Int` postulates -- same
        // order `clo_eq_ref_if_tree`/`call_eq_ref` both use.
        let quant_types = vec![None; n_captures + arity];
        let store = self.store;
        let ty = params_and_close_typed(self, &quant_types, kernel::close_pi, |combinators, pp| {
            let all = pp.at(&combinators.cp.arith);
            let (cs, ps) = all.split_at(n_captures);
            let call_fn_here = call_fn.at(&combinators.cp.arith);

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
            let pap_fn_here = pap_fn.at(&combinators.cp.arith);
            let g_env = if g_captures.is_empty() {
                None
            } else {
                let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
                let mk_env_expr = combinators.cp.mk_env_ref(&g_sig); // cache hit -- primed above
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

            let clo_ty = combinators.cp.clo_ty(k); // cache hit -- primed by pap_ref above
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
    fn ite_clo_eq_ref(&mut self, xc: i64, arity: usize) -> Expr {
        let key = (xc, arity);
        if let Some(&pos) = self.cp.ite_clo_eq_pos.get(&key) {
            return self.cp.arith.p.get(pos);
        }
        self.cp.arith.lit(xc);
        let clo_ty = self.cp.clo_ty(arity); // also primes ite_clo_ref(arity)
        let clo_ty = Anchored::new(&self.cp.arith, clo_ty);
        let ite_clo = self.cp.ite_clo_ref(arity);
        let ite_clo = Anchored::new(&self.cp.arith, ite_clo);
        let lit_xc = self.cp.arith.lit_ref(xc);
        let lit_xc = Anchored::new(&self.cp.arith, lit_xc);
        // `dt`/`de` : `Clo_arity` -- `params_and_close` itself can only
        // ever push `Int`-typed postulates (it doesn't even take a
        // `ClosureCombinators`), so this needs `params_and_close_typed`'s
        // own `Clo_k`-aware quantification instead.
        let quant_types = vec![Some(arity), Some(arity)];
        let ty = params_and_close_typed(self, &quant_types, kernel::close_pi, |combinators, pp| {
            let all = pp.at(&combinators.cp.arith);
            let (dt, de) = (all[0].clone(), all[1].clone());
            let clo_ty_here = clo_ty.at(&combinators.cp.arith);
            let ite_clo_here = ite_clo.at(&combinators.cp.arith);
            let lit_xc_here = lit_xc.at(&combinators.cp.arith);
            let lhs = kernel::app3(ite_clo_here, lit_xc_here, dt.clone(), de.clone());
            let rhs = if xc != 0 { dt } else { de };
            Some(kernel::id(clo_ty_here, lhs, rhs))
        })
        .expect("the build closure above always returns Some");
        let pos = self.cp.arith.p.push(ty);
        self.cp.ite_clo_eq_pos.insert(key, pos);
        self.cp.arith.p.get(pos)
    }

    /// Ties `apply_ref(k)` (`inner_root`'s own arity, `k`) to
    /// `inner_root`'s own closure *value* (whatever `register(inner_root)`
    /// produces): `apply_ref(k)(<inner_root's own value>(env?),
    /// p_{k-1}..p_0) = call_ref(inner_root)(env?, p_{k-1}..p_0)`,
    /// quantified over `inner_root`'s own captures then its own `k`
    /// params (same shape, same descending param order, as
    /// `call_eq_ref`'s own quantification), memoized by `inner_root`
    /// alone (`apply_ref(k)` itself stays memoized by `k`, shared across
    /// every closure of that arity). Honest for the same reason
    /// `call_eq_ref` is: `apply_ref`'s and `mk_clo_ref`'s combined meaning
    /// *is* "calling the closure that value represents", so relating it to
    /// `call_ref(inner_root)` (already pinned by `call_eq_ref`) states
    /// nothing new, just makes the connection kernel-checkable. See
    /// `clo_eq_ref`'s own docs for why every postulate this references
    /// must be primed *before* the quantified construction below, not
    /// lazily from inside it.
    fn apply_clo_eq_ref(&mut self, inner_root: Hash) -> Option<Expr> {
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

        let apply_fn = self.cp.apply_ref(arity);
        let apply_fn = Anchored::new(&self.cp.arith, apply_fn);
        let call_fn = self.call_ref(inner_root, &captures, &dummy_caller_param_types)?;
        let call_fn = Anchored::new(&self.cp.arith, call_fn);
        let value_fn = self.register(inner_root, &captures, &dummy_caller_param_types)?;
        let value_fn = Anchored::new(&self.cp.arith, value_fn);
        if n_captures > 0 {
            self.cp.mk_env_ref(&sig);
        }

        let quant_types = vec![None; n_captures + arity];
        let ty = params_and_close_typed(self, &quant_types, kernel::close_pi, |combinators, pp| {
            let all = pp.at(&combinators.cp.arith);
            let (cs, ps) = all.split_at(n_captures);
            let value_fn_here = value_fn.at(&combinators.cp.arith);
            let call_fn_here = call_fn.at(&combinators.cp.arith);
            let apply_fn_here = apply_fn.at(&combinators.cp.arith);

            let (closure_value, env_arg): (Expr, Option<Expr>) = if n_captures > 0 {
                let mk_env_expr = combinators.cp.mk_env_ref(&sig); // cache hit -- primed above
                let env = apply_n(mk_env_expr, cs.iter().cloned());
                (kernel::app(value_fn_here, env.clone()), Some(env))
            } else {
                (value_fn_here, None)
            };

            // LHS: `apply_ref(k)` has no separate `Env_sig` slot of its
            // own -- the environment, if any, is already folded into
            // `closure_value` itself (mirroring `apply_ref`'s own
            // postulated type, `Clo_k -> Int^k -> Int`).
            let mut apply_args = Vec::with_capacity(1 + arity);
            apply_args.push(closure_value);
            apply_args.extend(ps.iter().rev().cloned());
            let lhs = apply_n(apply_fn_here, apply_args);

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
    /// directly-registered combinator's: `apply_ref(k)(pap_ref(g,
    /// s)(g_env?, a_{s-1}..a_0), b_{k-1}..b_0) = call_ref(g)(g_env?,
    /// a_{s-1}..a_0, b_{k-1}..b_0)`, `k = g`'s own arity minus `s`.
    /// Needed because `pap_ref` is exactly as opaque as a directly-
    /// registered combinator's own value was before `apply_clo_eq_ref` --
    /// this is the semantic fact a compile-time-desugared PAP wrapper's
    /// own codegen encodes (`register_partial_app`'s wrapper forwards its
    /// own supplied arguments plus whatever further ones it's eventually
    /// given straight into `g`'s own entry), stated here as the only thing
    /// that gives `pap_ref`'s otherwise-opaque value defined behavior once
    /// something is actually applied to it. Restricted to `g`'s own
    /// params all being `Int`-typed, mirroring `clo_eq_ref_pap`'s own
    /// identical restriction (this axiom is only ever reached from there).
    /// Memoized by `(g, s)` alone -- `apply_ref(k)`/`pap_ref(g, s)` each
    /// stay memoized by their own key already.
    fn apply_pap_eq_ref(&mut self, g: Hash, s: usize) -> Option<Expr> {
        let key = (g, s);
        if let Some(&pos) = self.cp.apply_pap_eq_pos.get(&key) {
            return Some(self.cp.arith.p.get(pos));
        }
        let (g_arity, g_body, g_is_rec) = compile::peel(self.store, g)?;
        if s == 0 || s >= g_arity {
            return None;
        }
        let k = g_arity - s;
        let g_param_types = param_types_for(self.store, g)?;
        if g_param_types.iter().any(Option::is_some) {
            return None;
        }
        let g_captures = compile::free_vars(self.store, g_body, g_arity, g_is_rec);
        let n_captures = g_captures.len();
        let dummy_caller_param_types: Vec<Option<usize>> =
            vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
        let sig = capture_sig(&g_captures, &dummy_caller_param_types)?;

        let apply_fn = self.cp.apply_ref(k);
        let apply_fn = Anchored::new(&self.cp.arith, apply_fn);
        let call_fn = self.call_ref(g, &g_captures, &dummy_caller_param_types)?;
        let call_fn = Anchored::new(&self.cp.arith, call_fn);
        let pap_fn = self.pap_ref(g, s, &dummy_caller_param_types)?;
        let pap_fn = Anchored::new(&self.cp.arith, pap_fn);
        if n_captures > 0 {
            self.cp.mk_env_ref(&sig);
        }

        // Quantify `n_captures + g_arity` fresh `Int` postulates -- same
        // order (captures first, then `g`'s own `s` supplied params, then
        // its remaining `k`) `apply_clo_eq_ref`'s own quantification uses
        // for captures-then-params.
        let quant_types = vec![None; n_captures + g_arity];
        let ty = params_and_close_typed(self, &quant_types, kernel::close_pi, |combinators, pp| {
            let all = pp.at(&combinators.cp.arith);
            let (cs, ps) = all.split_at(n_captures);
            let (supplied, more) = ps.split_at(s);
            let pap_fn_here = pap_fn.at(&combinators.cp.arith);
            let call_fn_here = call_fn.at(&combinators.cp.arith);
            let apply_fn_here = apply_fn.at(&combinators.cp.arith);

            let (pap_value, env_arg): (Expr, Option<Expr>) = if n_captures > 0 {
                let mk_env_expr = combinators.cp.mk_env_ref(&sig); // cache hit -- primed above
                let env = apply_n(mk_env_expr, cs.iter().cloned());
                let v = apply_n(pap_fn_here, std::iter::once(env.clone()).chain(supplied.iter().cloned()));
                (v, Some(env))
            } else {
                (apply_n(pap_fn_here, supplied.iter().cloned()), None)
            };

            // LHS: `apply_ref(k)(pap_value, more_{k-1}..more_0)` -- same
            // descending order `apply_clo_eq_ref`'s own LHS uses for its
            // own `k` params.
            let mut apply_args = Vec::with_capacity(1 + k);
            apply_args.push(pap_value);
            apply_args.extend(more.iter().rev().cloned());
            let lhs = apply_n(apply_fn_here, apply_args);

            // RHS: `call_ref(g)(g_env?, a_0..a_{s-1}, b_{k-1}..b_0)` --
            // same combinator, `g`'s own full argument list in one call,
            // `env` (if any) leading. The `s` supplied args are *not*
            // reversed here, unlike `more`: they never pass through
            // `apply_ref`'s own convention at all (only `pap_fn`'s, on the
            // LHS, in the same unreversed order) -- so their own ordering
            // only has to agree between this axiom's LHS and RHS (and
            // whatever independently reconstructs the same value at a
            // call site, e.g. `eval_and_prove_call_over`'s own
            // `pap_at_denoted`), not with `call_ref`'s "descending"
            // convention the way `more` (which *does* cross `apply_ref`)
            // must.
            let mut call_args = Vec::with_capacity(1 + s + k);
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
enum ClosureRhsShape {
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
fn classify_closure_if_tree(store: &TermStore, h: Hash) -> DecisionTree {
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
/// closure creation in this position"). A leaf reached only through a
/// further *saturated* indirect call (`ClosureRhsShape::Call`'s own
/// shape) is a further, natural generalization, not attempted here.
enum ClosureIfTreeLeafShape {
    Abs { captures: Vec<u32> },
    Pap { g: Hash, args: Vec<Hash> },
}

/// Classifies one `IfTree` leaf `h`: a bare literal lambda (`Abs`,
/// captures via `free_vars`, `Term::Rec` excluded -- no proof-side
/// counterpart here, same restriction the original all-`Abs` check
/// already made), or a partial application `g(args)` of a further
/// literal lambda `g`, under-applied by exactly `k` (`root`'s own
/// expected `Clo` arity, already confirmed shared by every leaf via
/// `combinator_return_type`'s own recursion before `clo_eq_ref_if_tree`
/// is ever reached -- mirrors `clo_eq_ref_pap`'s own classification,
/// restricted the same way to `g`'s own params all being `Int`-typed).
/// `None` for anything else (a further nested `If`/`Rec`, an
/// unrecognized `App` shape).
fn classify_closure_if_tree_leaf(store: &TermStore, h: Hash, k: usize) -> Option<ClosureIfTreeLeafShape> {
    match store.resolve(h) {
        Term::Abs(_) => {
            let (inner_arity, inner_body, inner_is_rec) = compile::peel(store, h)?;
            let captures = compile::free_vars(store, inner_body, inner_arity, inner_is_rec);
            Some(ClosureIfTreeLeafShape::Abs { captures })
        }
        Term::App(..) => {
            let (g, args) = compile::unwind_app_spine(store, h);
            if !matches!(store.resolve(g), Term::Abs(_) | Term::Rec(_)) {
                return None;
            }
            let g_param_types = param_types_for(store, g)?;
            if g_param_types.iter().any(Option::is_some) {
                return None;
            }
            let g_arity = g_param_types.len();
            if args.len() >= g_arity || g_arity - args.len() != k {
                return None;
            }
            Some(ClosureIfTreeLeafShape::Pap { g, args })
        }
        _ => None,
    }
}

/// Every leaf of `tree`, classified via `classify_closure_if_tree_leaf`
/// (a leaf appearing more than once in the tree -- structurally
/// identical sub-terms, hash-consed together -- classified only once);
/// `None` if any leaf fails to classify.
fn classify_closure_if_tree_leaves(store: &TermStore, tree: &DecisionTree, k: usize) -> Option<HashMap<Hash, ClosureIfTreeLeafShape>> {
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
fn closure_if_tree_leaves(tree: &DecisionTree, out: &mut Vec<Hash>) {
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
fn collect_closure_if_tree_literals(store: &TermStore, tree: &DecisionTree, arity: usize, lits: &mut Vec<i64>) -> bool {
    match tree {
        DecisionTree::Leaf(_) => true,
        DecisionTree::If { cond, then_branch, else_branch } => {
            collect_literals(store, *cond, arity, None, None, lits)
                && collect_closure_if_tree_literals(store, then_branch, arity, lits)
                && collect_closure_if_tree_literals(store, else_branch, arity, lits)
        }
    }
}

/// Primes `register`/`mk_env_ref` for every `Abs`-shaped leaf, `pap_ref`/
/// `mk_env_ref` for every `Pap`-shaped one's own `g` -- mirrors
/// `clo_eq_ref_if_tree`'s own single-pair `prime_inner` (`Abs` case) and
/// `clo_eq_ref_pap`'s own priming (`Pap` case), generalized to every leaf
/// `leaf_shapes` (from `classify_closure_if_tree_leaves`) names.
fn prime_closure_if_tree_leaves(combinators: &mut ClosureCombinators<'_>, leaf_shapes: &HashMap<Hash, ClosureIfTreeLeafShape>) -> Option<()> {
    for (&h, shape) in leaf_shapes {
        match shape {
            ClosureIfTreeLeafShape::Abs { captures } => {
                let dummy: Vec<Option<usize>> = vec![None; captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
                combinators.register(h, captures, &dummy)?;
                if !captures.is_empty() {
                    let sig = capture_sig(captures, &dummy)?;
                    combinators.cp.mk_env_ref(&sig);
                }
            }
            ClosureIfTreeLeafShape::Pap { g, args } => {
                let (g_arity, g_body, g_is_rec) = compile::peel(combinators.store, *g)?;
                let g_captures = compile::free_vars(combinators.store, g_body, g_arity, g_is_rec);
                let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
                combinators.pap_ref(*g, args.len(), &g_dummy)?;
                if !g_captures.is_empty() {
                    let g_sig = capture_sig(&g_captures, &g_dummy)?;
                    combinators.cp.mk_env_ref(&g_sig);
                }
            }
        }
    }
    Some(())
}

/// An `Abs`-shaped leaf's own `register`/`mk_env_ref` value expression,
/// over abstract `params_full` -- `clo_eq_ref_if_tree`'s own single-pair
/// `value_expr`, generalized to read a leaf's own captures from
/// `captures` (from `leaf_shapes`) instead of a locally-closed-over pair.
fn closure_leaf_value_expr(combinators: &mut ClosureCombinators<'_>, leaf: Hash, captures: &[u32], params_full: &[Expr]) -> Option<Expr> {
    let dummy: Vec<Option<usize>> = vec![None; captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let sym = combinators.register(leaf, captures, &dummy)?; // cache hit -- primed above
    if captures.is_empty() {
        Some(sym)
    } else {
        let sig: Vec<Option<usize>> = vec![None; captures.len()];
        let mk_env_expr = combinators.cp.mk_env_ref(&sig); // cache hit -- primed above
        let cs2: Vec<Expr> = captures.iter().map(|&rel| params_full[rel as usize].clone()).collect();
        Some(kernel::app(sym, apply_n(mk_env_expr, cs2)))
    }
}

/// A `Pap`-shaped leaf's own `pap_ref`/`mk_env_ref` value expression,
/// over abstract `params_full` -- mirrors `clo_eq_ref_pap`'s own
/// RHS-formula construction exactly (same `pap_ref(g,s)(g_env?,
/// denote(args, params_full)...)`), just built over `root`'s own
/// abstract quantified vars here instead of a fresh `Pi`'s own.
fn closure_leaf_pap_value_expr(store: &TermStore, combinators: &mut ClosureCombinators<'_>, g: Hash, args: &[Hash], params_full: &[Expr]) -> Option<Expr> {
    let (g_arity, g_body, g_is_rec) = compile::peel(store, g)?;
    let g_captures = compile::free_vars(store, g_body, g_arity, g_is_rec);
    let s = args.len();
    let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let pap_fn = combinators.pap_ref(g, s, &g_dummy)?; // cache hit -- primed by prime_closure_if_tree_leaves
    let g_env = if g_captures.is_empty() {
        None
    } else {
        let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
        let mk_env_expr = combinators.cp.mk_env_ref(&g_sig); // cache hit -- primed above
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

/// `clo_eq_ref_if_tree`'s own axiom RHS, built recursively over `tree`:
/// `ite_clo_k(denote(cond, params_full), <then's value>, <else's value>)`
/// at every internal node, bottoming out at each leaf's own value
/// expression (`closure_leaf_value_expr` for `Abs`,
/// `closure_leaf_pap_value_expr` for `Pap`, dispatched via
/// `leaf_shapes`). Mirrors `denote_with_placeholders`'s own `Term::If`
/// (`Clo` branches) case structurally, generalized from one step to the
/// whole tree.
fn build_closure_if_tree_rhs(
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
        },
        DecisionTree::If { cond, then_branch, else_branch } => {
            let dc = denote(store, *cond, &combinators.cp.arith, params_full)?;
            let dt = build_closure_if_tree_rhs(store, combinators, then_branch, leaf_shapes, params_full, k)?;
            let de = build_closure_if_tree_rhs(store, combinators, else_branch, leaf_shapes, params_full, k)?;
            let ite_clo = combinators.cp.ite_clo_ref(k); // cache hit -- primed by clo_ty(k) above
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
fn inner_closure_pap_value(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    g: Hash,
    args: &[Hash],
    inner_params: &[Anchored],
    inner_concrete: &[i64],
    inner_facts: &[Anchored],
) -> Option<(Expr, ValueTriples, ValueTriples)> {
    let (g_arity, g_body, g_is_rec) = compile::peel(store, g)?;
    let g_captures = compile::free_vars(store, g_body, g_arity, g_is_rec);
    let s = args.len();

    let mut g_cap_triples = Vec::with_capacity(g_captures.len());
    for &rel in &g_captures {
        let rel = rel as usize;
        let x = *inner_concrete.get(rel)?;
        let d = Anchored::new(&combinators.cp.arith, inner_params.get(rel)?.at(&combinators.cp.arith));
        let p = Anchored::new(&combinators.cp.arith, inner_facts.get(rel)?.at(&combinators.cp.arith));
        g_cap_triples.push((x, d, p));
    }

    let mut supplied_triples = Vec::with_capacity(s);
    for &a in args {
        let (x, d, p) = eval_and_prove(store, a, combinators, inner_params, inner_concrete, inner_facts)?;
        supplied_triples.push((x, Anchored::new(&combinators.cp.arith, d), Anchored::new(&combinators.cp.arith, p)));
    }

    let g_dummy: Vec<Option<usize>> = vec![None; g_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let pap_fn = combinators.pap_ref(g, s, &g_dummy)?; // cache hit -- primed by prime_closure_if_tree_leaves
    let g_env_denoted = if g_cap_triples.is_empty() {
        None
    } else {
        let g_sig: Vec<Option<usize>> = vec![None; g_captures.len()];
        let mk_env_expr = combinators.cp.mk_env_ref(&g_sig); // cache hit -- primed above
        let cd: Vec<Expr> = g_cap_triples.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)).collect();
        Some(apply_n(mk_env_expr, cd))
    };
    let d_supplied: Vec<Expr> = supplied_triples.iter().map(|(_, d, _)| d.at(&combinators.cp.arith)).collect();
    let mut pap_args = Vec::with_capacity(1 + s);
    pap_args.extend(g_env_denoted);
    pap_args.extend(d_supplied);
    let pap_value = apply_n(pap_fn, pap_args);
    Some((pap_value, g_cap_triples, supplied_triples))
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
fn closure_if_tree_value_at_literals(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    tree: &DecisionTree,
    leaf_shapes: &HashMap<Hash, ClosureIfTreeLeafShape>,
    inner_params: &[Anchored],
    inner_concrete: &[i64],
    inner_facts: &[Anchored],
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
        },
        DecisionTree::If { cond, then_branch, else_branch } => {
            let params_full: Vec<Expr> = inner_params.iter().map(|a| a.at(&combinators.cp.arith)).collect();
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
#[allow(clippy::type_complexity, clippy::too_many_arguments)]
fn resolve_closure_if_tree(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    tree: &DecisionTree,
    leaf_shapes: &HashMap<Hash, ClosureIfTreeLeafShape>,
    inner_params: &[Anchored],
    inner_concrete: &[i64],
    inner_facts: &[Anchored],
    k: usize,
) -> Option<(Hash, ValueTriples, ValueTriples, Expr, Expr, Expr)> {
    match tree {
        DecisionTree::Leaf(h) => {
            let (chosen, cap_triples, arg_prefix, value_lit) = match leaf_shapes.get(h)? {
                ClosureIfTreeLeafShape::Abs { .. } => {
                    let (value_lit, cap_triples) = inner_closure_literal_value(combinators, *h, inner_params, inner_concrete, inner_facts)?;
                    (*h, cap_triples, Vec::new(), value_lit)
                }
                ClosureIfTreeLeafShape::Pap { g, args } => {
                    let (value_lit, g_cap_triples, supplied_triples) =
                        inner_closure_pap_value(store, combinators, *g, args, inner_params, inner_concrete, inner_facts)?;
                    (*g, g_cap_triples, supplied_triples, value_lit)
                }
            };
            let value_lit = Anchored::new(&combinators.cp.arith, value_lit);
            let value_lit = value_lit.at(&combinators.cp.arith);
            let proof = kernel::refl(value_lit.clone());
            Some((chosen, cap_triples, arg_prefix, value_lit.clone(), value_lit, proof))
        }
        DecisionTree::If { cond, then_branch, else_branch } => {
            let (result_c, denote_c, proof_c) = eval_and_prove(store, *cond, combinators, inner_params, inner_concrete, inner_facts)?;
            let denote_c = Anchored::new(&combinators.cp.arith, denote_c);
            let proof_c = Anchored::new(&combinators.cp.arith, proof_c);

            let (taken, other) = if result_c != 0 { (then_branch, else_branch) } else { (else_branch, then_branch) };
            let (chosen, chosen_cap_triples, chosen_arg_prefix, taken_subtree_value, leaf_value, taken_proof) =
                resolve_closure_if_tree(store, combinators, taken, leaf_shapes, inner_params, inner_concrete, inner_facts, k)?;
            let taken_subtree_value = Anchored::new(&combinators.cp.arith, taken_subtree_value);
            let leaf_value = Anchored::new(&combinators.cp.arith, leaf_value);
            let taken_proof = Anchored::new(&combinators.cp.arith, taken_proof);
            let other_value = closure_if_tree_value_at_literals(store, combinators, other, leaf_shapes, inner_params, inner_concrete, inner_facts, k)?;
            let other_value = Anchored::new(&combinators.cp.arith, other_value);

            combinators.cp.arith.lit(result_c);
            let ite_eq_axiom = combinators.ite_clo_eq_ref(result_c, k);
            let ite_eq_axiom = Anchored::new(&combinators.cp.arith, ite_eq_axiom);

            // Nothing pushes past here -- resolve everything fresh, in
            // one batch, only once nothing more is left to push.
            let denote_c = denote_c.at(&combinators.cp.arith);
            let proof_c = proof_c.at(&combinators.cp.arith);
            let taken_subtree_value = taken_subtree_value.at(&combinators.cp.arith);
            let leaf_value = leaf_value.at(&combinators.cp.arith);
            let taken_proof = taken_proof.at(&combinators.cp.arith);
            let other_value = other_value.at(&combinators.cp.arith);
            let ite_eq_axiom = ite_eq_axiom.at(&combinators.cp.arith);
            let lit_xc = combinators.cp.arith.lit_ref(result_c);
            let ite_clo = combinators.cp.ite_clo_ref(k); // cache hit -- primed by clo_eq_ref via clo_ty(k)
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
            let ite_at_denote_c = kernel::app3(ite_clo.clone(), denote_c, dt.clone(), de.clone());
            let ite_at_lit_xc = kernel::app3(ite_clo, lit_xc, dt.clone(), de.clone());

            let ite_axiom_at = apply_n(ite_eq_axiom, vec![dt, de]);
            let branch_bridge = kernel::trans_proof(&clo_ty, &ite_at_denote_c, &ite_at_lit_xc, &taken_subtree_value, cong_cond, ite_axiom_at);
            let this_subtree_value = ite_at_denote_c;
            let full_proof = kernel::trans_proof(&clo_ty, &this_subtree_value, &taken_subtree_value, &leaf_value, branch_bridge, taken_proof);

            Some((chosen, chosen_cap_triples, chosen_arg_prefix, this_subtree_value, leaf_value, full_proof))
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
        match classify_app_node(store, h, param_types)? {
            // A parameter-typed closure, called through `call_indirect`:
            // per compile.rs's own typed dispatch, arguments are always
            // `Int` regardless of the callee's own signature.
            AppShape::ParamCall { root, k, args } => {
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
            // call, `AppShape::LitLambdaExact`), fewer arguments than its
            // own arity (compile.rs's compile-time-desugared partial
            // application, `register_partial_app`'s wrapper,
            // `AppShape::LitLambdaPartial` -- `pap_ref` covers a
            // self-recursive root here too, the same opaque-call reasoning),
            // or more (`AppShape::LitLambdaOver`: `root`'s own saturated
            // call is built first, exactly as the direct-call case does,
            // then whatever it denotes is dispatched on the extra
            // arguments via `apply_ref`, exactly like the `ParamCall` case
            // above -- see `combinator_return_type`'s own docs for why
            // this is sound without denoting `root`'s body in the usual
            // sense). Each argument's expected type matches the *callee's
            // own* parameter type at that position (`Clo` or `Int`), which
            // is what lets e.g. `twice(inc, 5)` pass a closure and a plain
            // `Int` to the same call.
            AppShape::LitLambdaPartial { root, args, callee_param_types } => {
                // Compile-time-desugared partial application: build
                // mk_pap_root_k(a_1,...,a_k), a Clo-typed value -- see
                // pap_ref's own docs for why the supplied arguments are
                // denoted normally here rather than resolved through any
                // Env/build_env_expr-style machinery (unlike root's
                // *own* environment, when it captures, which does need
                // build_env_expr, exactly as a direct call to a
                // capturing root does below).
                let arity = callee_param_types.len();
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
            AppShape::LitLambdaExact { root, args, callee_param_types } | AppShape::LitLambdaOver { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
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
                // `ParamCall` case above), just with the callee freshly
                // computed rather than read from `params`. Only sound
                // when that result genuinely denotes a further `Clo` --
                // unlike compile.rs (which has no type system to check
                // this at all, relying entirely on jit.rs's sample
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
        params.push(pos);
    }

    let denoted = denote_closure(store, body, &mut combinators, &params, &param_types)?;
    // `result_ty` mirrors `denoted`'s own tag: `Int`'s postulate for a
    // `Denoted::Int`, or the specific `Clo_k` for a `Denoted::Clo` --
    // `k` re-derived structurally via `return_type_of` applied to the
    // whole body (no self-call concept at this top level, so `self_idx`
    // is `None`, same as the nested-`If` case in `denote_closure` itself),
    // kept in lockstep with every `Denoted::Clo`-producing shape
    // `denote_closure` recognizes -- see `return_type_of`'s own docs.
    // `clo_ty(k)` here is always a cache hit, never a fresh push:
    // `denote_closure` itself already had to call `clo_ty(k)` for this
    // exact `k` somewhere while building `denoted`, to type its own
    // `debug_assert_has_type` checks along the way.
    let (result_ty, denotation) = match denoted {
        Denoted::Int(e) => (combinators.cp.arith.int_ty(), e),
        Denoted::Clo(e) => {
            let k = return_type_of(store, body, arity, None, &param_types).flatten()?;
            (combinators.cp.clo_ty(k), e)
        }
    };
    let proof = kernel::refl(denotation.clone());
    let proof_ty = kernel::id(result_ty.clone(), denotation.clone(), denotation.clone());
    kernel::check(&combinators.cp.arith.p.ctx, &proof, &proof_ty).ok()?;

    Some(EquivalenceProof {
        ctx: combinators.cp.arith.p.ctx,
        arity,
        result_ty,
        denotation,
        proof,
    })
}

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
// `compile_node`'s own call convention and the interpreter's own
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
struct ConcreteClo {
    root: Hash,
    frame: Vec<DynVal>,
}

/// One frame slot's own concretely-known value, threaded through
/// `eval_dyn`'s walk -- the per-instance analogue of `denote_closure`'s
/// `params`/`param_types` pair. Every slot here is `Anchored` rather than
/// a raw postulate position (contrast `denote_closure`'s `params:
/// &[usize]`): a substituted value (an inlined callee's own parameter,
/// or a closure's own captured value read back later) is an arbitrary
/// compound expression, not a fresh, unsubstituted postulate -- exactly
/// the case `Anchored` exists for (see its own docs). Every `Int` slot
/// also carries its own concrete numeral, for concretely following an
/// `If`'s own condition the same way `classify_step` already does.
#[derive(Clone)]
enum DynVal {
    Int(Anchored, i64),
    Clo(Anchored, Rc<ConcreteClo>),
}

/// `denote_closure`'s per-instance counterpart to `Denoted`: a `Clo` here
/// additionally carries its own `ConcreteClo` -- *which* literal lambda
/// this concretely is, and the frame to resolve its own captures against
/// -- since a per-instance proof, unlike the universal one, can actually
/// answer that question. Holds `Anchored`, not a raw `Expr` (contrast
/// `Denoted`): `eval_dyn` frequently builds several of these (e.g. one
/// per argument at a call site) *before* they're all actually consumed,
/// and a call site's own further construction (`call_ref`, `clo_ty`, ...)
/// may lazily push more postulates in between -- exactly the staleness
/// class `Anchored`'s own docs describe, just one level up from a single
/// built term to this enum's own payload. Anchoring at construction, not
/// at first use, is what `denote_closure` already does for its own
/// `Denoted` values at each composite case's own boundary; this does the
/// same, just carried in the type itself since `eval_dyn`'s own values
/// routinely outlive more than one such case.
enum DynDenoted {
    Int(Anchored),
    Clo(Anchored, Rc<ConcreteClo>),
}

/// Projects `frame` down to plain `i64`s, for `eval_concrete`'s own
/// `params: &[i64]` convention -- used only to resolve an `If`'s own
/// condition concretely. A `Clo` slot has no meaningful projection (a
/// well-typed condition never references one); `0` is an arbitrary
/// placeholder, never legitimately read -- if it somehow were, the
/// resulting proof attempt would fail `kernel::check` later rather than
/// silently proving something false, the same "sound, not complete"
/// tolerance this whole fragment already has for a malformed input.
fn dyn_frame_concrete_ints(frame: &[DynVal]) -> Vec<i64> {
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
fn dyn_frame_to_env(store: &TermStore, frame: &[DynVal]) -> Option<eval::Env> {
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
/// resolves, which `compile_cond`'s own restriction guarantees never
/// embed a call), this argument may itself be an application of a
/// concretely-known closure (e.g. a loop-carried `g(x)`), which
/// `eval_concrete`'s own fragment (`Var`/`Lit`/`Prim`/`If` only) can't
/// evaluate at all. Rather than re-derive a second concrete evaluator for
/// applications, this defers to the reference interpreter itself
/// (`eval::eval`) over an `Env` rebuilt from `frame` (`dyn_frame_to_env`)
/// -- the same ground truth this whole project already judges every
/// other representation against, so reusing it here needs no separate
/// argument for why it's correct.
fn eval_concrete_dyn(store: &TermStore, h: Hash, frame: &[DynVal]) -> Option<i64> {
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
fn dyn_frame_param_types(store: &TermStore, frame: &[DynVal]) -> Option<Vec<Option<usize>>> {
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
fn collect_literals_dyn(store: &TermStore, h: Hash, out: &mut Vec<i64>) {
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
/// own `Anchored` value rather than a raw postulate position (see
/// `DynVal`'s own docs for why a substituted slot needs this).
fn build_env_expr_dyn(store: &TermStore, combinators: &mut ClosureCombinators, captures: &[u32], frame: &[DynVal]) -> Option<Expr> {
    let frame_types = dyn_frame_param_types(store, frame)?;
    let sig = capture_sig(captures, &frame_types)?;
    let mut values = Vec::with_capacity(captures.len());
    for &rel in captures {
        let e = match frame.get(rel as usize)? {
            DynVal::Int(a, _) => a.at(&combinators.cp.arith),
            DynVal::Clo(a, _) => a.at(&combinators.cp.arith),
        };
        values.push(Anchored::new(&combinators.cp.arith, e));
    }
    let mk_env_expr = combinators.cp.mk_env_ref(&sig);
    let mk_env = Anchored::new(&combinators.cp.arith, mk_env_expr);
    let mk_env = mk_env.at(&combinators.cp.arith);
    let values: Vec<Expr> = values.iter().map(|v| v.at(&combinators.cp.arith)).collect();
    Some(apply_n(mk_env, values))
}

/// Bounds how much work following one concrete `eval_dyn` trace may do,
/// shared (via `&mut`) across the whole walk, including through mutual
/// recursion with `eval_dyn` itself (see its own docs). Two separate
/// counters, not one, because they bound genuinely different things:
/// `tail_steps` bounds `eval_dyn_tail_recursive`'s own flat loop --
/// unaffected by whether any *non*-tail self-call is also present, since
/// the loop itself never recurses through Rust's own call stack, so a
/// generous bound (matching `prove_tail_recursive_call`'s own) costs
/// nothing extra; `recursion_depth` separately bounds how many *embedded*
/// (non-tail) self-calls `eval_dyn` may follow, since -- unlike the tail
/// loop -- each one genuinely recurses through Rust's own call stack
/// (`eval_dyn` calling back into `eval_dyn_tail_recursive`, which may
/// itself call back into `eval_dyn` for the next embedded self-call), so
/// this needs a much smaller bound to stay well clear of a real stack
/// overflow -- see `eval.rs`'s own docs on the same native-stack limit
/// for non-tail recursion (~8,000-10,000 levels there, for far lighter
/// per-frame work than building up a kernel proof term does).
struct DynBudget {
    tail_steps: usize,
    recursion_depth: usize,
}

impl DynBudget {
    fn new() -> Self {
        DynBudget { tail_steps: 10_000, recursion_depth: 50 }
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
/// followed, bounded by `budget.recursion_depth` separately from this
/// loop's own `budget.tail_steps`.
///
/// `combinators`' `register`/`call_ref` memoization is keyed by `Hash`
/// alone (see `eval_dyn_direct_call`'s own docs on this) -- safe here as
/// long as any one literal reached from more than one iteration is
/// always denoted from the same frame each time, true whenever a
/// closure-typed parameter is simply threaded through the loop unchanged
/// (this function's own reason for existing) rather than replaced by a
/// freshly created one with different captures partway through.
fn eval_dyn_tail_recursive(
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
        if budget.tail_steps == 0 {
            return None;
        }
        budget.tail_steps -= 1;
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
fn eval_dyn_direct_call(
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
        if !compile::free_vars(store, root_body, root_arity, root_is_rec).is_empty() {
            return None; // scoped out -- see this function's own docs
        }
        let mut child: Vec<Option<DynVal>> = vec![None; root_arity];
        for (j, (v, &a)) in arg_vals.into_iter().zip(args.iter()).enumerate() {
            let pos = root_arity - 1 - j;
            child[pos] = Some(match v {
                // `e` is already `Anchored` (built no later than this
                // call's own `arg_vals` loop above) -- safe to carry
                // into the child frame unchanged; `DynVal`'s own `.at()`
                // will reshift it correctly whenever it's eventually
                // resolved, however much more gets pushed in between.
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
        return eval_dyn(store, root_body, combinators, None, budget, &child);
    }

    // Ordinary opaque call: mirrors `denote_closure`'s own
    // `LitLambdaExact` construction exactly, just resolving `root`'s own
    // captures against `root_frame` instead of a raw `params: &[usize]`.
    // Every sub-piece (`call_fn`, `env_expr`, each `arg_exprs` entry) is
    // already `Anchored` (either just-built here, or carried in from
    // `arg_vals` above) -- nothing is resolved via `.at()` until every
    // last lazy push (`call_ref`, `build_env_expr_dyn`, `clo_ty` below)
    // is done, the same discipline `denote_closure`'s own composite
    // cases already follow.
    let captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
    let root_frame_types = dyn_frame_param_types(store, root_frame)?;
    let call_fn = combinators.call_ref(root, &captures, &root_frame_types)?;
    let call_fn = Anchored::new(&combinators.cp.arith, call_fn);
    let env_expr = if captures.is_empty() {
        None
    } else {
        let e = build_env_expr_dyn(store, combinators, &captures, root_frame)?;
        Some(Anchored::new(&combinators.cp.arith, e))
    };
    let mut arg_exprs = Vec::with_capacity(root_arity);
    for (j, v) in arg_vals.into_iter().enumerate() {
        let pos = root_arity - 1 - j;
        let e = match (root_param_types[pos], v) {
            (Some(_), DynDenoted::Clo(e, _)) => e,
            (None, DynDenoted::Int(e)) => e,
            _ => return None, // unreachable: needs_inline was false above
        };
        arg_exprs.push(e);
    }
    let call_fn = call_fn.at(&combinators.cp.arith);
    let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
    if let Some(env_expr) = &env_expr {
        all_args.push(env_expr.at(&combinators.cp.arith));
    }
    all_args.extend(arg_exprs.iter().map(|a| a.at(&combinators.cp.arith)));
    let applied = apply_n(call_fn, all_args);
    let applied = Anchored::new(&combinators.cp.arith, applied);
    // `return_ty` was already checked above: `needs_inline` is true
    // whenever it's `Some`, so this opaque path -- reached only when
    // `needs_inline` was false -- always has a plain `Int` result here.
    debug_assert!(return_ty.is_none(), "a Clo-returning root should always have been inlined above");
    let int_ty = combinators.cp.arith.int_ty();
    let applied_resolved = applied.at(&combinators.cp.arith);
    debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied_resolved, &int_ty, "eval_dyn: direct combinator call");
    Some(DynDenoted::Int(applied))
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
/// actually reached -- bounded by `budget.recursion_depth` (see
/// `DynBudget`'s own docs for why that's a separate, much smaller bound
/// than `eval_dyn_tail_recursive`'s own flat-loop one). A *branching*
/// non-tail shape (more than one self-call in the same leaf, e.g.
/// `f(n-1) + f(n-2)`) falls out of this for free -- each occurrence is
/// just another embedded self-call, evaluated independently -- but is
/// exponential in trace length the same way any per-instance trace of a
/// branching recursive shape is, so it's only practical for the small,
/// fixed samples this whole methodology is ever run against, never a
/// substitute for `prove_tail_recursive_universal`'s own genuine
/// induction on shapes it already covers.
fn eval_dyn(store: &TermStore, h: Hash, combinators: &mut ClosureCombinators, self_ctx: Option<(Hash, usize)>, budget: &mut DynBudget, frame: &[DynVal]) -> Option<DynDenoted> {
    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        let concrete = dyn_frame_concrete_ints(frame);
        let cv = eval_concrete(store, c, &concrete)?;
        return eval_dyn(store, if cv != 0 { t } else { e }, combinators, self_ctx, budget, frame);
    }

    if matches!(store.resolve(h), Term::App(..)) {
        let (root, args) = compile::unwind_app_spine(store, h);
        if let Term::Var(i) = store.resolve(root)
            && let Some((self_body, self_arity)) = self_ctx
            && *i as usize == self_arity
            && args.len() == self_arity
        {
            // An embedded (non-tail) self-call -- see this function's
            // own docs.
            if budget.recursion_depth == 0 {
                return None;
            }
            budget.recursion_depth -= 1;
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
            return eval_dyn_tail_recursive(store, self_body, self_arity, combinators, budget, new_frame);
        }
        return match store.resolve(root) {
            Term::Var(i) => {
                let DynVal::Clo(_, cc) = frame.get(*i as usize)?.clone() else { return None };
                let cc_root = cc.root;
                let cc_frame = cc.frame.clone();
                eval_dyn_direct_call(store, combinators, cc_root, &cc_frame, &args, self_ctx, budget, frame)
            }
            Term::Abs(_) | Term::Rec(_) => eval_dyn_direct_call(store, combinators, root, frame, &args, self_ctx, budget, frame),
            _ => None,
        };
    }

    match store.resolve(h) {
        // `e` is already `Anchored` (from `DynVal`) -- pass it through
        // unchanged rather than resolving now, so it stays safe to hold
        // across whatever this read's own caller does before actually
        // consuming it.
        Term::Var(i) => {
            if let Some((_, self_arity)) = self_ctx
                && *i as usize == self_arity
            {
                // A bare reference to the enclosing self-recursive value
                // itself, not applied -- out of scope structurally, the
                // same restriction `compile.rs`'s own `free_vars` places
                // on capturing a self-reference as a plain value from a
                // nested closure.
                return None;
            }
            match frame.get(*i as usize)?.clone() {
                DynVal::Int(e, _) => Some(DynDenoted::Int(e)),
                DynVal::Clo(e, cc) => Some(DynDenoted::Clo(e, cc)),
            }
        }
        Term::Lit(n) => Some(DynDenoted::Int(Anchored::new(&combinators.cp.arith, combinators.cp.arith.lit_ref(*n)))),
        Term::Prim(op, a, b) => {
            let (op, a, b) = (*op, *a, *b);
            let DynDenoted::Int(da) = eval_dyn(store, a, combinators, self_ctx, budget, frame)? else { return None };
            let DynDenoted::Int(db) = eval_dyn(store, b, combinators, self_ctx, budget, frame)? else { return None };
            let op_ref = combinators.cp.arith.op_ref(op); // pre-postulated once -- never pushes
            let da = da.at(&combinators.cp.arith);
            let db = db.at(&combinators.cp.arith);
            let applied = kernel::app2(op_ref, da, db);
            let int_ty = combinators.cp.arith.int_ty();
            debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &int_ty, "eval_dyn: Prim");
            Some(DynDenoted::Int(Anchored::new(&combinators.cp.arith, applied)))
        }
        Term::Abs(_) | Term::Rec(_) => {
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
                return Some(DynDenoted::Clo(Anchored::new(&combinators.cp.arith, sym), cc));
            }
            // `register` (just above) already primes `clo_ty(arity)` as
            // part of building `mk_clo_ref`'s own type, so the explicit
            // `clo_ty(arity)` call below is a cache hit, never a fresh
            // push -- safe to resolve `sym`/`env_expr` fresh immediately
            // before it, the same ordering `denote_closure`'s identical
            // case already relies on.
            let sym = Anchored::new(&combinators.cp.arith, sym);
            let env = build_env_expr_dyn(store, combinators, &captures, frame)?;
            let env_expr = Anchored::new(&combinators.cp.arith, env);
            let sym = sym.at(&combinators.cp.arith);
            let env_expr = env_expr.at(&combinators.cp.arith);
            let applied = kernel::app(sym, env_expr);
            let clo_ty = combinators.cp.clo_ty(arity);
            debug_assert_has_type(&combinators.cp.arith.p.ctx, &applied, &clo_ty, "eval_dyn: capturing closure value");
            let applied = Anchored::new(&combinators.cp.arith, applied);
            Some(DynDenoted::Clo(applied, cc))
        }
        Term::If(..) | Term::App(..) => unreachable!("handled above"),
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
        frame.push(DynVal::Int(Anchored::new(&combinators.cp.arith, e), n));
    }

    let mut budget = DynBudget::new();
    let denoted = if is_rec {
        eval_dyn_tail_recursive(store, body, arity, &mut combinators, &mut budget, frame)?
    } else {
        eval_dyn(store, body, &mut combinators, None, &mut budget, &frame)?
    };
    // `result_ty` first (its own `clo_ty(k)` may push, for an arity not
    // otherwise seen while building `denoted`), `denotation` resolved
    // fresh only afterward -- the same ordering `prove_closure_expr`'s
    // own identical step already relies on.
    let (result_ty, denotation) = match denoted {
        DynDenoted::Int(e) => (combinators.cp.arith.int_ty(), e.at(&combinators.cp.arith)),
        DynDenoted::Clo(e, cc) => {
            let (k, _, _) = compile::peel(store, cc.root)?;
            let ty = combinators.cp.clo_ty(k);
            (ty, e.at(&combinators.cp.arith))
        }
    };
    let proof = kernel::refl(denotation.clone());
    let proof_ty = kernel::id(result_ty.clone(), denotation.clone(), denotation.clone());
    kernel::check(&combinators.cp.arith.p.ctx, &proof, &proof_ty).ok()?;

    Some(EquivalenceProof {
        ctx: combinators.cp.arith.p.ctx,
        arity,
        result_ty,
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
        )
        .expect("the recorded proof should independently re-typecheck");

        // This term is also handled by the interpreter and the WASM
        // compiler -- all three paths agree on which terms are in scope.
        assert!(compile::try_compile(&s, f).is_some());
    }

    /// **Architecture prototype, not wired into `ClosurePostulates`.**
    /// Investigates whether the whole `Clo_k`-as-a-family-of-opaque-
    /// `Sort(0)`-postulates scheme (`ClosurePostulates::clo_ty`/
    /// `apply_ref`/`ite_clo_ref`, one fresh axiom pair per distinct arity a
    /// term uses) could instead be built from the *literal* curried
    /// `Int -> .. -> Int` arrow type -- no new postulate at all -- reusing
    /// `Int` (already postulated by `ArithPostulates`) and `bool_rec`
    /// (already postulated, generically, by `kernel::NatPostulates`) rather
    /// than adding anything new. Confirms three things a real migration
    /// would need:
    ///
    /// 1. A `Clo_k`-shaped value (an opaque postulated constant of the
    ///    literal arrow type) can be called directly via ordinary
    ///    `kernel::app`, typechecking as `Int` with no `apply_ref` axiom at
    ///    all -- `apply_ref`'s entire reason to exist (relating an opaque
    ///    `Clo_k` to a callable shape) turns out to be unnecessary once
    ///    `Clo_k` genuinely *is* that shape.
    /// 2. `bool_rec` instantiated at a *constant* motive (`\_:Bool. A`) is a
    ///    real `ite : Bool -> A -> A -> A` for any `A`, with its
    ///    computation-rule axioms (`bool_rec_true_eq`/`bool_rec_false_eq`)
    ///    already proving `ite`'s own -- no per-arity `ite_clo_k` family
    ///    needed either.
    /// 3. Two different arities are still genuinely distinct types --
    ///    `kernel::check` rejects a `Clo_3`-shaped value where a `Clo_2` is
    ///    expected, for free, from ordinary Pi-type structural inequality --
    ///    so this doesn't reopen the arity-blind-`Clo` unsoundness
    ///    `TYPES.md` section 6.2 documents.
    ///
    /// See the design investigation this answers in `RELATED_WORK.md`.
    #[test]
    fn a_curried_int_arrow_can_stand_in_for_clo_k_with_zero_new_postulates() {
        fn curried_arrow(int_ty: &Expr, k: usize) -> Expr {
            let mut ty = int_ty.clone();
            for _ in 0..k {
                ty = kernel::arrow(int_ty.clone(), ty);
            }
            ty
        }

        let mut arith = ArithPostulates::new();
        let nat = kernel::NatPostulates::new(&mut arith.p);

        // Push every postulate this prototype needs *first* -- two opaque
        // arity-2 closure values (f, g, exactly like
        // `ClosureCombinators::combinator_value`'s own postulated
        // constant), two opaque Ints to call the chosen one with, and one
        // opaque arity-3 closure value (h, for the arity-mismatch check) --
        // then resolve every reference fresh in one final pass with no
        // further pushes in between. Interleaving a `p.get` with a later
        // `p.push` would go stale (exactly the `Anchored`-staleness bug
        // class `RELATED_WORK.md` documents: a `Var`'s correct de Bruijn
        // index depends on how many postulates exist *right now*, and this
        // prototype hit that bug on its first run, confirming the class is
        // just as live here as anywhere else in this project).
        let f_pos = arith.p.push(curried_arrow(&arith.int_ty(), 2));
        let g_pos = arith.p.push(curried_arrow(&arith.int_ty(), 2));
        let a_pos = arith.p.push(arith.int_ty());
        let b_pos = arith.p.push(arith.int_ty());
        let h_pos = arith.p.push(curried_arrow(&arith.int_ty(), 3));

        // Now resolve everything fresh, with no more pushes to follow.
        let int_ty = arith.int_ty();
        let clo2_ty = curried_arrow(&int_ty, 2);
        let clo3_ty = curried_arrow(&int_ty, 3);
        assert_ne!(clo2_ty, clo3_ty, "different arities must stay genuinely distinct types");

        let f = arith.p.get(f_pos);
        let g = arith.p.get(g_pos);
        let a = arith.p.get(a_pos);
        let b = arith.p.get(b_pos);
        let h = arith.p.get(h_pos);

        // A generic `ite`, derived (not postulated) from `bool_rec`
        // instantiated at the constant motive `\_:Bool. Clo2`.
        let bool_ty = nat.bool_ty(&arith.p);
        let const_motive = kernel::lam(bool_ty, kernel::shift(&clo2_ty, 0, 1));
        let cond = nat.true_(&arith.p);
        let chosen = kernel::app(
            kernel::app3(nat.bool_rec(&arith.p), const_motive.clone(), f.clone(), g.clone()),
            cond,
        );
        kernel::check(&arith.p.ctx, &chosen, &clo2_ty).expect("ite(Clo2, true, f, g) should typecheck at Clo2");

        // Calling it directly through ordinary `App` -- no `apply_ref`
        // postulate anywhere in this construction at all.
        let called = kernel::app2(chosen.clone(), a, b);
        kernel::check(&arith.p.ctx, &called, &int_ty)
            .expect("calling a Clo2-shaped value with 2 Ints should typecheck as Int, with no apply_ref axiom");

        // The computation rule (`ite(true) = f`) is already derivable from
        // `bool_rec_true_eq` at this instantiation -- no new `ite_true_eq`
        // postulate needed either.
        let true_eq_generic = nat.bool_rec_true_eq(&arith.p);
        let instantiated = kernel::app3(true_eq_generic, const_motive, f.clone(), g.clone());
        let expected_ty = kernel::id(clo2_ty.clone(), chosen, f);
        kernel::check(&arith.p.ctx, &instantiated, &expected_ty)
            .expect("bool_rec_true_eq, instantiated at Clo2, should already prove ite(Clo2,true,f,g) = f");

        // Arity mismatch is still rejected: a Clo3-shaped value can't stand
        // in where a Clo2 is expected -- the soundness gain `TYPES.md`
        // section 6.2/7 documents survives this representation change.
        assert!(
            kernel::check(&arith.p.ctx, &h, &clo2_ty).is_err(),
            "a Clo3-shaped value must still be rejected where a Clo2 is expected"
        );
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
                &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
        // now succeeds here too: `eval_and_prove`'s own `call_eq_ref`
        // computation-rule axiom (see its docs) covers exactly this shape
        // -- a self-call argument that creates and calls a *capturing*
        // literal lambda (`root`'s own single capture, `acc`, resolved
        // against the outer, all-`Int` frame) whose body is a single
        // `Prim` node.
        assert_eq!(eval::apply_term(&s, h, &[5, 0]).unwrap(), 15, "interpreter sanity check: 5+4+3+2+1");
        let instance = prove_tail_recursive_instance(&s, h, &[5, 0])
            .expect("a self-call argument creating and calling a capturing closure should now get a concrete instance");
        kernel::check(&instance.ctx, &instance.proof, &kernel::id(instance.int_ty.clone(), instance.lhs.clone(), instance.rhs.clone()))
            .expect("the recorded instance proof should independently re-typecheck");

        assert!(compile::try_compile(&s, h).is_some());
    }

    #[test]
    fn eval_and_prove_call_respects_call_refs_own_argument_order_for_a_non_symmetric_root() {
        // A wrong argument order in `call_eq_ref`'s own axiom construction
        // (or in `eval_and_prove_call`'s own instantiation of it) would
        // still typecheck -- every position here is `Int`, so a swapped
        // axiom is just a *different*, still well-typed, universally
        // quantified fact -- so only comparing the *concrete value*
        // against an independent interpretation (not `kernel::check`
        // alone) can catch it. `x - y` is non-commutative, so swapping
        // `x`/`y` gives a visibly wrong answer rather than one that
        // happens to coincide. This calls the private `eval_and_prove`
        // directly (this module's own test submodule can) rather than
        // going through a full self-recursive scaffold, since the bug
        // this guards is local to `eval_and_prove_call` itself.
        let mut s = TermStore::new();
        let x = s.var(1); // first-applied
        let y = s.var(0); // last-applied
        let diff = s.prim(PrimOp::Sub, x, y);
        let inner = s.abs(diff);
        let root = s.abs(inner);
        let five = s.lit(5);
        let three = s.lit(3);
        let applied_to_x = s.app(root, five);
        let h = s.app(applied_to_x, three);

        assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), 2, "interpreter sanity check: 5 - 3 = 2");

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(5);
        combinators.cp.arith.lit(3);
        let (result, denotation, proof) = eval_and_prove(&s, h, &mut combinators, &[], &[], &[])
            .expect("a non-capturing literal-lambda self-call-argument should get a concrete witness");
        assert_eq!(result, 2, "eval_and_prove_call must not swap call_ref's own argument order");
        kernel::check(
            &combinators.cp.arith.p.ctx,
            &proof,
            &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(2)),
        )
        .expect("the recorded witness should independently re-typecheck");
    }

    #[test]
    fn eval_and_prove_call_over_gets_a_concrete_instance_for_the_canonical_if_between_closures_shape() {
        // f = \a b. if 0 < a then (\c. a+b+c) else (\c. a-b+c); f(a,b,c) --
        // the exact same canonical over-application shape as
        // `an_over_applied_literal_lambda_returning_a_closure_gets_a_closure_proof`,
        // now also checked for a concrete instance (both branches of the
        // `If`), via `clo_eq_ref`/`ite_clo_eq_ref`/`apply_clo_eq_ref`.
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
        let f_body = s.if_(cond, closure1, closure2);
        let f_inner = s.abs(f_body);
        let f = s.abs(f_inner);

        for (a_val, b_val, c_val, expected) in [(10, 3, 100, 113), (-5, 3, 100, 92)] {
            let a_lit = s.lit(a_val);
            let b_lit = s.lit(b_val);
            let c_lit = s.lit(c_val);
            let fa = s.app(f, a_lit);
            let fab = s.app(fa, b_lit);
            let h = s.app(fab, c_lit);

            assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), expected, "interpreter sanity check");

            let mut combinators = ClosureCombinators::new(&s);
            combinators.cp.arith.lit(a_val);
            combinators.cp.arith.lit(b_val);
            combinators.cp.arith.lit(c_val);
            let (result, denotation, proof) = eval_and_prove(&s, h, &mut combinators, &[], &[], &[])
                .expect("an over-applied literal lambda returning an If-chosen closure should get a concrete witness");
            assert_eq!(result, expected);
            kernel::check(
                &combinators.cp.arith.p.ctx,
                &proof,
                &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
            )
            .expect("the recorded witness should independently re-typecheck");
        }
    }

    #[test]
    fn eval_and_prove_call_over_respects_apply_refs_own_argument_order_for_a_non_symmetric_root() {
        // f = \a. if 0<a then (\c d. c-d) else (\c d. d-c); f(a,c,d) -- k=2
        // extra arguments, non-commutative in each branch. `k=1` (the
        // canonical shape above) has no argument order to get wrong at
        // all, so this is the one that actually exercises
        // `apply_clo_eq_ref`'s own descending `p_{k-1}..p_0`
        // instantiation, the same reason the `call_eq_ref` pass's own
        // regression test used a 2-arg root.
        let mut s = TermStore::new();
        let d1 = s.var(0);
        let c1 = s.var(1);
        let cd1 = s.prim(PrimOp::Sub, c1, d1);
        let closure1_inner = s.abs(cd1);
        let closure1 = s.abs(closure1_inner); // \c d. c - d

        let c2 = s.var(1);
        let d2 = s.var(0);
        let dc2 = s.prim(PrimOp::Sub, d2, c2);
        let closure2_inner = s.abs(dc2);
        let closure2 = s.abs(closure2_inner); // \c d. d - c

        let a_body = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, a_body);
        let f_body = s.if_(cond, closure1, closure2);
        let f = s.abs(f_body); // \a. if 0<a then closure1 else closure2

        for (a_val, c_val, d_val, expected) in [(5, 10, 3, 7), (-5, 10, 3, -7)] {
            let a_lit = s.lit(a_val);
            let c_lit = s.lit(c_val);
            let d_lit = s.lit(d_val);
            let fa = s.app(f, a_lit);
            let fac = s.app(fa, c_lit);
            let h = s.app(fac, d_lit);

            assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), expected, "interpreter sanity check");

            let mut combinators = ClosureCombinators::new(&s);
            combinators.cp.arith.lit(a_val);
            combinators.cp.arith.lit(c_val);
            combinators.cp.arith.lit(d_val);
            let (result, denotation, proof) = eval_and_prove(&s, h, &mut combinators, &[], &[], &[])
                .expect("a non-symmetric over-applied closure call should get a concrete witness");
            assert_eq!(result, expected, "eval_and_prove_call_over must not swap apply_ref's own argument order");
            kernel::check(
                &combinators.cp.arith.p.ctx,
                &proof,
                &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
            )
            .expect("the recorded witness should independently re-typecheck");
        }
    }

    #[test]
    fn eval_and_prove_call_over_resolves_an_inner_closures_own_captures_against_roots_frame_not_double_shifted() {
        // f = \a. if 0<a then (\c. a+w+c) else (\c. a-w-c), where `w` is
        // captured by `f` itself from an outer frame -- `t`/`e` (the two
        // inner closures) each *also* capture something from `f`'s own
        // frame (`a`, f's own param, *and* `w`, f's own capture, at
        // different absolute positions). An off-by-`root_arity` double
        // shift when indexing `t`/`e`'s own captures into `params_full`
        // (mistakenly adding `f`'s own arity on top of the relative index
        // `compile::free_vars` already gives, by analogy with how `f`'s
        // *own* captures genuinely do need that shift) would read the
        // wrong slot and produce a visibly wrong value here, not a
        // rejection -- `eval::apply_term` is the independent check.
        let mut s = TermStore::new();
        let c1 = s.var(0); // t's own param
        let a1 = s.var(1); // f's own param, one level deeper than in f's own body
        let w1 = s.var(2); // f's own capture, one level deeper than in f's own body
        let aw1 = s.prim(PrimOp::Add, a1, w1);
        let awc1 = s.prim(PrimOp::Add, aw1, c1);
        let closure_t = s.abs(awc1); // \c. a + w + c

        let c2 = s.var(0);
        let a2 = s.var(1);
        let w2 = s.var(2);
        let aw2 = s.prim(PrimOp::Sub, a2, w2);
        let awc2 = s.prim(PrimOp::Sub, aw2, c2);
        let closure_e = s.abs(awc2); // \c. a - w - c

        let a_body = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, a_body);
        let f_body = s.if_(cond, closure_t, closure_e);
        let f = s.abs(f_body); // \a. if 0<a then closure_t else closure_e -- captures `w`

        for (w_val, a_val, c_val, expected) in [(100, 10, 5, 115), (100, -10, 5, -115)] {
            let a_lit = s.lit(a_val);
            let c_lit = s.lit(c_val);
            let fa = s.app(f, a_lit);
            let h = s.app(fa, c_lit); // h's own only free variable is `w`, at Var(0)
            let h_closed = s.abs(h); // eval::apply_term expects a function value, not a bare free variable

            assert_eq!(eval::apply_term(&s, h_closed, &[w_val]).unwrap(), expected, "interpreter sanity check");

            let mut combinators = ClosureCombinators::new(&s);
            combinators.cp.arith.lit(w_val);
            let w_lit = combinators.cp.arith.lit_ref(w_val);
            let w_param = Anchored::new(&combinators.cp.arith, w_lit.clone());
            let w_fact = Anchored::new(&combinators.cp.arith, kernel::refl(w_lit));
            combinators.cp.arith.lit(a_val);
            combinators.cp.arith.lit(c_val);
            let (result, denotation, proof) = eval_and_prove(&s, h, &mut combinators, &[w_param], &[w_val], &[w_fact])
                .expect("an inner closure capturing both root's own param and root's own capture should get a concrete witness");
            assert_eq!(result, expected, "eval_and_prove_call_over must resolve an inner closure's own captures against root's frame directly, not double-shifted by root's own arity");
            kernel::check(
                &combinators.cp.arith.p.ctx,
                &proof,
                &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
            )
            .expect("the recorded witness should independently re-typecheck");
        }
    }

    #[test]
    fn a_pap_producing_root_gets_a_concrete_instance_for_eval_and_prove_call_over() {
        // g = \x y. x*10 + y (arity 2, deliberately asymmetric so an
        // index-order bug between x/y would change the result, not just
        // its symmetry); f = \a. g(a) -- f's own saturated call is a
        // *partial application* of g (root_arity=1, k=1, per
        // `return_type_of`'s own `Ordering::Less` branch), not an `If`
        // between two closures -- `clo_eq_ref_pap` (not
        // `clo_eq_ref_if_between`) covers this shape now. `f(a)(c)` is
        // over-application: `f`'s own saturated call denotes `g` partially
        // applied to `a`, then the extra argument `c` completes it, so the
        // whole term should agree with calling `g(a, c)` directly.
        let mut s = TermStore::new();
        let x = s.var(1);
        let y = s.var(0);
        let ten = s.lit(10);
        let x10 = s.prim(PrimOp::Mul, x, ten);
        let xy = s.prim(PrimOp::Add, x10, y);
        let g_inner = s.abs(xy);
        let g = s.abs(g_inner);

        let a_ref = s.var(0);
        let f_body = s.app(g, a_ref);
        let f = s.abs(f_body); // \a. g(a) -- a PAP of g, arity 1

        let a_lit = s.lit(5);
        let c_lit = s.lit(3);
        let fa = s.app(f, a_lit);
        let h = s.app(fa, c_lit);

        // Hand-verified against the reference interpreter before trusting
        // the term shape, per this project's own established discipline:
        // g(5, 3) = 5*10 + 3 = 53 (an index swap would instead give
        // g(3, 5) = 3*10 + 5 = 35, a different number, so this is a real
        // regression guard, not just a symmetry check).
        assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), 53);

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(5);
        combinators.cp.arith.lit(3);
        let (result, denoted, proof) =
            eval_and_prove(&s, h, &mut combinators, &[], &[], &[]).expect("a PAP-producing root's over-application should get a concrete instance");
        assert_eq!(result, 53, "should agree with the reference interpreter, not just typecheck");
        let int_ty = combinators.cp.arith.int_ty();
        kernel::check(&combinators.cp.arith.p.ctx, &proof, &kernel::id(int_ty, denoted, combinators.cp.arith.lit_ref(result)))
            .expect("the recorded proof should independently re-typecheck");
    }

    #[test]
    fn a_further_indirectly_called_combinator_gets_a_concrete_instance_for_eval_and_prove_call_over() {
        // h = \p q. p*10 + q (arity 2, asymmetric coefficients so an
        // index-order bug changes the result, not just its symmetry);
        // middle = \b. h(b) -- a PAP of h (arity 1, `middle`'s own
        // saturated call returns `Clo_1`); root = \x y. middle(y) -- arity
        // 2, `x` a decoy left unused so a `root`-level saturating-args
        // order bug (e.g. `build_clo_call_bridge`'s own inner-frame
        // construction) swaps in `x`'s own value where `y`'s belongs,
        // catchably -- calls `middle` *saturated* (middle's own arity is
        // 1, matching `args.len()`), so this is `ClosureRhsShape::Call`,
        // not `Pap`: `root`'s own body doesn't itself hold the literal
        // lambda that will eventually be called, only a further,
        // statically-known indirection to one (`middle`, itself
        // Clo-returning) -- the "further nested-call-producing root"
        // shape. `root(x)(y)(c)` is over-application: `root`'s own
        // saturated call denotes `middle`'s own saturated call (itself a
        // further `Clo_1`), and *that* denotes `h` partially applied to
        // `y`; the extra argument `c` completes it, so the whole term
        // should agree with `h(y, c)` directly (never `x`).
        let mut s = TermStore::new();
        let p = s.var(1);
        let q = s.var(0);
        let ten = s.lit(10);
        let p10 = s.prim(PrimOp::Mul, p, ten);
        let pq = s.prim(PrimOp::Add, p10, q);
        let h_inner = s.abs(pq);
        let h = s.abs(h_inner); // \p q. p*10 + q

        let b_ref = s.var(0);
        let middle_body = s.app(h, b_ref);
        let middle = s.abs(middle_body); // \b. h(b) -- a PAP of h, arity 1

        let y_ref = s.var(0);
        let root_body = s.app(middle, y_ref);
        let root_y_binder = s.abs(root_body);
        let root = s.abs(root_y_binder); // \x y. middle(y) -- a saturated call to middle, arity 2

        let x_lit = s.lit(100); // decoy: must never influence the result
        let y_lit = s.lit(7);
        let c_lit = s.lit(2);
        let root_x = s.app(root, x_lit);
        let root_xy = s.app(root_x, y_lit);
        let h_term = s.app(root_xy, c_lit);

        // Hand-verified against the reference interpreter before trusting
        // the term shape, per this project's own established discipline:
        // h(7, 2) = 7*10 + 2 = 72 (an index swap would instead give
        // h(2, 7) = 27, or pick up the decoy `x` for a very different
        // number like h(100, 2) = 1002).
        assert_eq!(eval::apply_term(&s, h_term, &[]).unwrap(), 72);

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(100);
        combinators.cp.arith.lit(7);
        combinators.cp.arith.lit(2);
        let (result, denoted, proof) = eval_and_prove(&s, h_term, &mut combinators, &[], &[], &[])
            .expect("a further indirectly-called combinator's over-application should get a concrete instance");
        assert_eq!(result, 72, "should agree with the reference interpreter, not just typecheck");
        let int_ty = combinators.cp.arith.int_ty();
        kernel::check(&combinators.cp.arith.p.ctx, &proof, &kernel::id(int_ty, denoted, combinators.cp.arith.lit_ref(result)))
            .expect("the recorded proof should independently re-typecheck");
    }

    #[test]
    fn two_levels_of_further_indirection_still_get_a_concrete_instance() {
        // h = \p q. p - q (arity 2, asymmetric so an operand-order bug
        // changes the result); middle = \b. h(b) -- a PAP of h, arity 1;
        // outer = \a. middle(a) -- `Call`, one level of indirection (as
        // the test above); root = \a. outer(a) -- *another* saturated
        // call to a further Clo-returning combinator, since
        // `combinator_return_type(outer)` itself recurses through
        // `outer`'s own `Call` shape to find `Some(1)` -- a *second*
        // `Call` layer, confirming `resolve_closure_shape_to_leaf`'s own
        // recursion isn't hardcoded to depth 1. `root(a)(c)` should agree
        // with `h(a, c)` directly, chaining through `outer` and `middle`
        // both.
        let mut s = TermStore::new();
        let p = s.var(1);
        let q = s.var(0);
        let pq = s.prim(PrimOp::Sub, p, q);
        let h_inner = s.abs(pq);
        let h = s.abs(h_inner); // \p q. p - q

        let b_ref = s.var(0);
        let middle_body = s.app(h, b_ref);
        let middle = s.abs(middle_body); // \b. h(b)

        let a_ref1 = s.var(0);
        let outer_body = s.app(middle, a_ref1);
        let outer = s.abs(outer_body); // \a. middle(a)

        let a_ref2 = s.var(0);
        let root_body = s.app(outer, a_ref2);
        let root = s.abs(root_body); // \a. outer(a)

        let a_lit = s.lit(11);
        let c_lit = s.lit(4);
        let root_a = s.app(root, a_lit);
        let h_term = s.app(root_a, c_lit);

        // Hand-verified against the reference interpreter first: h(11,4)
        // = 11-4 = 7 (the operand-swapped h(4,11) = -7 would be a clearly
        // different, wrong number).
        assert_eq!(eval::apply_term(&s, h_term, &[]).unwrap(), 7);

        let mut combinators = ClosureCombinators::new(&s);
        combinators.cp.arith.lit(11);
        combinators.cp.arith.lit(4);
        let (result, denoted, proof) =
            eval_and_prove(&s, h_term, &mut combinators, &[], &[], &[]).expect("two levels of further indirection should still get a concrete instance");
        assert_eq!(result, 7, "should agree with the reference interpreter, not just typecheck");
        let int_ty = combinators.cp.arith.int_ty();
        kernel::check(&combinators.cp.arith.p.ctx, &proof, &kernel::id(int_ty, denoted, combinators.cp.arith.lit_ref(result)))
            .expect("the recorded proof should independently re-typecheck");
    }

    #[test]
    fn a_pap_producing_root_with_two_supplied_args_and_a_capturing_g_gets_a_concrete_instance() {
        // g = \p q r. p*100 + q*10 + r + captured_y (arity 3), where
        // `captured_y` is a *capture*, not one of g's own params --
        // relative to g's own 3-ary scope that's `Var(3)` (one beyond p/q/r,
        // `p`=Var(2)/`q`=Var(1)/`r`=Var(0) innermost-last), which resolves
        // (per `free_vars`' own "no additional shift" convention for a
        // lambda referenced directly, with no binders of its own in
        // between) to `f`'s own `y` -- `g_x` sits immediately inside `f`'s
        // body, introducing no binders of its own before that point.
        // Fully asymmetric coefficients so any swap among the *two* args
        // `f` itself supplies (p, q), the one extra arg (r), or the
        // captured value (`y`, doubly used: both a supplied arg *and* a
        // capture) changes the result.
        //
        // f = \x y. g(x, y) -- a PAP of g supplying 2 of its 3 remaining
        // params (s=2, k=1), specifically exercising the *ordering among
        // the supplied args themselves* (the single-supplied-arg test
        // above can't distinguish this, since reversing one element is a
        // no-op) together with `g`'s own capture.
        let mut s = TermStore::new();
        let p = s.var(2);
        let q = s.var(1);
        let r = s.var(0);
        let captured_y = s.var(3);
        let hundred = s.lit(100);
        let ten = s.lit(10);
        let p100 = s.prim(PrimOp::Mul, p, hundred);
        let q10 = s.prim(PrimOp::Mul, q, ten);
        let sum1 = s.prim(PrimOp::Add, p100, q10);
        let sum2 = s.prim(PrimOp::Add, sum1, r);
        let sum3 = s.prim(PrimOp::Add, sum2, captured_y);
        let g_r = s.abs(sum3);
        let g_q = s.abs(g_r);
        let g_p = s.abs(g_q); // g = \p q r. p*100+q*10+r+captured_y, capturing Var(3) relative to its own arity-3 scope

        let f_x = s.var(1);
        let f_y = s.var(0);
        let f_body = s.app2(g_p, f_x, f_y); // g(x, y) -- a 2-of-3 partial application of g
        let f_y_binder = s.abs(f_body);
        let f = s.abs(f_y_binder); // f = \x y. g(x, y), arity 2

        let x_lit = s.lit(5);
        let y_lit = s.lit(7);
        let r_lit = s.lit(3);
        let f_at_x = s.app(f, x_lit);
        let f_at_x_y = s.app(f_at_x, y_lit);
        let h = s.app(f_at_x_y, r_lit); // ((f(x))(y))(r) -- f(x,y)'s own saturated call is the PAP, r is the over-application

        // Hand-verified: g(p=5,q=7,r=3,captured_y=7) = 5*100+7*10+3+7 = 580.
        // Swapping p/q would instead give 7*100+5*10+3+7 = 760.
        assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), 580);

        let mut combinators = ClosureCombinators::new(&s);
        for lit in [5, 7, 3] {
            combinators.cp.arith.lit(lit);
        }
        let (result, denoted, proof) =
            eval_and_prove(&s, h, &mut combinators, &[], &[], &[]).expect("a capturing PAP-producing root's over-application should get a concrete instance");
        assert_eq!(result, 580, "should agree with the reference interpreter, not just typecheck");
        let int_ty = combinators.cp.arith.int_ty();
        kernel::check(&combinators.cp.arith.p.ctx, &proof, &kernel::id(int_ty, denoted, combinators.cp.arith.lit_ref(result)))
            .expect("the recorded proof should independently re-typecheck");
    }

    #[test]
    fn a_further_nested_if_inside_a_branch_gets_a_concrete_instance_for_eval_and_prove_call_over() {
        // f = \a. if 0<a then (if a>10 then (\c. c) else (\c. c+1)) else (\c. c-1)
        // -- `t` is itself a further `If`, not a bare `Term::Abs` -- a
        // depth-2 decision tree, not the depth-1 `clo_eq_ref_if_between`
        // (now `clo_eq_ref_if_tree`) originally supported. Three leaves,
        // exercising all of them: the identity closure (`a>10`), `c+1`
        // (`0<a<=10`), and `c-1` (`a<=0`).
        let mut s = TermStore::new();
        let c1 = s.var(0);
        let one = s.lit(1);
        let c_plus_1 = s.prim(PrimOp::Add, c1, one);
        let inner_then = s.abs(c_plus_1);
        let c2 = s.var(0);
        let inner_else = s.abs(c2);
        let a_body1 = s.var(0);
        let ten = s.lit(10);
        let inner_cond = s.prim(PrimOp::Lt, ten, a_body1);
        let t = s.if_(inner_cond, inner_else, inner_then); // if a>10 then (\c.c) else (\c.c+1)

        let c3 = s.var(0);
        let one2 = s.lit(1);
        let c_minus_1 = s.prim(PrimOp::Sub, c3, one2);
        let e = s.abs(c_minus_1);

        let a_body2 = s.var(0);
        let zero = s.lit(0);
        let outer_cond = s.prim(PrimOp::Lt, zero, a_body2);
        let f_body = s.if_(outer_cond, t, e);
        let f = s.abs(f_body);

        // Hand-verified against the reference interpreter before trusting
        // the term shape: a=5 (0<a, a<=10) -> c+1 = 4; a=20 (0<a, a>10) ->
        // c = 3; a=-5 (a<=0) -> c-1 = 2.
        for (a_val, c_val, expected) in [(5, 3, 4), (20, 3, 3), (-5, 3, 2)] {
            let a_lit = s.lit(a_val);
            let c_lit = s.lit(c_val);
            let fa = s.app(f, a_lit);
            let h = s.app(fa, c_lit);
            assert_eq!(eval::apply_term(&s, h, &[]).unwrap(), expected, "a={a_val} c={c_val}: interpreter sanity check");

            let mut combinators = ClosureCombinators::new(&s);
            combinators.cp.arith.lit(a_val);
            combinators.cp.arith.lit(c_val);
            let (result, denotation, proof) = eval_and_prove(&s, h, &mut combinators, &[], &[], &[])
                .unwrap_or_else(|| panic!("a={a_val} c={c_val}: a further-nested If inside a branch should get a concrete instance"));
            assert_eq!(result, expected, "a={a_val} c={c_val}: should agree with the reference interpreter, not just typecheck");
            kernel::check(
                &combinators.cp.arith.p.ctx,
                &proof,
                &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
            )
            .unwrap_or_else(|e| panic!("a={a_val} c={c_val}: the recorded witness should independently re-typecheck: {e}"));
        }
    }

    #[test]
    fn an_if_tree_leaf_that_is_itself_a_partial_application_gets_a_concrete_instance() {
        // h = \p q r. p*100 + q*10 + r (arity 3, fully asymmetric
        // coefficients so any permutation of the three args changes the
        // result, not just its symmetry); root = \a b1 b2. if 0<a then
        // h(b1,b2) else (\c. c-1) -- arity 3, the `then` branch
        // (`h(b1,b2)`) is a *partial application* of a further literal
        // lambda h (two of its three args supplied), not a bare
        // `Term::Abs` -- previously out of scope
        // (`closure_if_tree_leaves_are_abs`'s own restriction), now
        // `ClosureIfTreeLeafShape::Pap`. `root(a,b1,b2)(c)` is
        // over-application (k=1): when `0<a`, the whole term should
        // agree with `h(b1, b2, c)` directly (asymmetric enough that a
        // supplied-args order bug in `chosen_arg_prefix`'s own handling
        // would give a different, wrong number, not just fail to
        // typecheck); otherwise with `c-1` (the `else` branch, still a
        // bare `Abs` leaf, exercising both shapes in the same tree).
        let mut s = TermStore::new();
        let p = s.var(2);
        let q = s.var(1);
        let r = s.var(0);
        let hundred = s.lit(100);
        let ten = s.lit(10);
        let p100 = s.prim(PrimOp::Mul, p, hundred);
        let q10 = s.prim(PrimOp::Mul, q, ten);
        let p100q10 = s.prim(PrimOp::Add, p100, q10);
        let pqr = s.prim(PrimOp::Add, p100q10, r);
        let h_inner2 = s.abs(pqr);
        let h_inner1 = s.abs(h_inner2);
        let h = s.abs(h_inner1); // \p q r. p*100 + q*10 + r

        let b1_ref = s.var(1);
        let b2_ref = s.var(0);
        let h_b1 = s.app(h, b1_ref);
        let then_branch = s.app(h_b1, b2_ref); // h(b1, b2) -- a Pap of h, arity 1

        let c1 = s.var(0);
        let one = s.lit(1);
        let c_minus_1 = s.prim(PrimOp::Sub, c1, one);
        let else_branch = s.abs(c_minus_1); // \c. c-1 -- a bare Abs leaf

        let a_ref = s.var(2);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, a_ref);
        let root_body = s.if_(cond, then_branch, else_branch);
        let root_b2_binder = s.abs(root_body);
        let root_b1_binder = s.abs(root_b2_binder);
        let root = s.abs(root_b1_binder); // \a b1 b2. if 0<a then h(b1,b2) else (\c.c-1)

        // Hand-verified against the reference interpreter before trusting
        // the term shape: a=5 (0<a) with b1=3,b2=7,c=2 ->
        // h(3,7,2) = 3*100+7*10+2 = 372 (h(7,3,2) = 732 would be a clearly
        // different, wrong number, catching a supplied-args order bug);
        // a=-5 (a<=0) with b1=3,b2=7 (unused, decoys),c=2 -> c-1=1.
        for (a_val, b1_val, b2_val, c_val, expected) in [(5, 3, 7, 2, 372), (-5, 3, 7, 2, 1)] {
            let a_lit = s.lit(a_val);
            let b1_lit = s.lit(b1_val);
            let b2_lit = s.lit(b2_val);
            let c_lit = s.lit(c_val);
            let root_a = s.app(root, a_lit);
            let root_ab1 = s.app(root_a, b1_lit);
            let root_ab1b2 = s.app(root_ab1, b2_lit);
            let h_term = s.app(root_ab1b2, c_lit);
            assert_eq!(
                eval::apply_term(&s, h_term, &[]).unwrap(),
                expected,
                "a={a_val} b1={b1_val} b2={b2_val} c={c_val}: interpreter sanity check"
            );

            let mut combinators = ClosureCombinators::new(&s);
            combinators.cp.arith.lit(a_val);
            combinators.cp.arith.lit(b1_val);
            combinators.cp.arith.lit(b2_val);
            combinators.cp.arith.lit(c_val);
            let (result, denotation, proof) = eval_and_prove(&s, h_term, &mut combinators, &[], &[], &[]).unwrap_or_else(|| {
                panic!("a={a_val} b1={b1_val} b2={b2_val} c={c_val}: a Pap-shaped IfTree leaf should get a concrete instance")
            });
            assert_eq!(
                result, expected,
                "a={a_val} b1={b1_val} b2={b2_val} c={c_val}: should agree with the reference interpreter, not just typecheck"
            );
            kernel::check(
                &combinators.cp.arith.p.ctx,
                &proof,
                &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
            )
            .unwrap_or_else(|e| panic!("a={a_val} b1={b1_val} b2={b2_val} c={c_val}: the recorded witness should independently re-typecheck: {e}"));
        }
    }

    #[test]
    fn a_self_recursive_root_whose_body_never_actually_self_calls_gets_a_concrete_instance() {
        // rec helper a = if 0<a then (\c. c+a) else (\c. c-a) -- arity 1,
        // wrapped in `Term::Rec` (syntactically self-recursive), but its
        // own body never actually references the self-binder anywhere.
        // Previously declined outright by `clo_eq_ref`'s own blanket
        // `if is_rec { return None; }` check regardless of whether `body`
        // genuinely used the self-reference; now `compile::free_vars`'s
        // own `is_rec`-aware capture computation is threaded through
        // instead, and a term like this one -- which never actually needs
        // it -- gets a concrete instance same as a non-recursive root
        // would. `helper(a)(c)` is over-application (k=1): the whole term
        // should agree with `a+c` (0<a) or `c-a` (a<=0) directly.
        let mut s = TermStore::new();
        let a_ref1 = s.var(0);
        let c1 = s.var(0);
        let a_shifted1 = s.var(1);
        let c_plus_a = s.prim(PrimOp::Add, c1, a_shifted1);
        let then_branch = s.abs(c_plus_a); // \c. c+a

        let c2 = s.var(0);
        let a_shifted2 = s.var(1);
        let c_minus_a = s.prim(PrimOp::Sub, c2, a_shifted2);
        let else_branch = s.abs(c_minus_a); // \c. c-a

        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, a_ref1);
        let helper_body = s.if_(cond, then_branch, else_branch);
        let helper_abs = s.abs(helper_body); // \a. if 0<a then (\c.c+a) else (\c.c-a)
        let helper = s.rec(helper_abs); // rec-wrapped, never actually self-calling

        // Hand-verified against the reference interpreter before trusting
        // the term shape: a=5 (0<a) with c=3 -> c+a=8; a=-5 (a<=0) with
        // c=10 -> c-a=15 -- distinct numbers, so picking the wrong branch
        // would be caught, not masked by a coincidental match.
        for (a_val, c_val, expected) in [(5, 3, 8), (-5, 10, 15)] {
            let a_lit = s.lit(a_val);
            let c_lit = s.lit(c_val);
            let helper_a = s.app(helper, a_lit);
            let h_term = s.app(helper_a, c_lit);
            assert_eq!(eval::apply_term(&s, h_term, &[]).unwrap(), expected, "a={a_val} c={c_val}: interpreter sanity check");

            let mut combinators = ClosureCombinators::new(&s);
            combinators.cp.arith.lit(a_val);
            combinators.cp.arith.lit(c_val);
            let (result, denotation, proof) = eval_and_prove(&s, h_term, &mut combinators, &[], &[], &[])
                .unwrap_or_else(|| panic!("a={a_val} c={c_val}: a self-recursive root that never self-calls should get a concrete instance"));
            assert_eq!(result, expected, "a={a_val} c={c_val}: should agree with the reference interpreter, not just typecheck");
            kernel::check(
                &combinators.cp.arith.p.ctx,
                &proof,
                &kernel::id(combinators.cp.arith.int_ty(), denotation, combinators.cp.arith.lit_ref(expected)),
            )
            .unwrap_or_else(|e| panic!("a={a_val} c={c_val}: the recorded witness should independently re-typecheck: {e}"));
        }
    }

    #[test]
    fn an_over_application_with_the_wrong_number_of_extra_args_is_out_of_scope() {
        // f = \a. if 0<a then (\c d. c-d) else (\c d. d-c) -- k=2, but
        // called with only 1 extra argument (a partial dispatch against
        // the chosen closure) -- `AppShape::LitLambdaOver`'s own
        // `args.len() != root_arity + k` guard should reject this.
        let mut s = TermStore::new();
        let d1 = s.var(0);
        let c1 = s.var(1);
        let cd1 = s.prim(PrimOp::Sub, c1, d1);
        let closure1_inner = s.abs(cd1);
        let closure1 = s.abs(closure1_inner);
        let c2 = s.var(1);
        let d2 = s.var(0);
        let dc2 = s.prim(PrimOp::Sub, d2, c2);
        let closure2_inner = s.abs(dc2);
        let closure2 = s.abs(closure2_inner);
        let a_body = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, a_body);
        let f_body = s.if_(cond, closure1, closure2);
        let f = s.abs(f_body);

        let a_lit = s.lit(5);
        let c_lit = s.lit(10);
        let fa = s.app(f, a_lit);
        let h = s.app(fa, c_lit); // only 1 extra arg, k=2 expected

        let mut combinators = ClosureCombinators::new(&s);
        assert!(
            eval_and_prove(&s, h, &mut combinators, &[], &[], &[]).is_none(),
            "an under-applied over-application should stay out of scope, not panic"
        );
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

        // `prove_tail_recursive_instance` no longer needs an explicit
        // `kernel::with_shift_cache` wrapper here -- `instance_from_scaffold`
        // now decides automatically, from a cheap dry run of how many
        // distinct nodes *this concrete instance* actually visits
        // (`instance_visit_count`), not just the function's own shape (see
        // its own docs for why shape alone wasn't enough). n=8 crosses
        // that threshold; independently re-typechecking the already-built
        // proof below is a separate call outside `instance_from_scaffold`,
        // so it still opts in explicitly regardless of n.
        for n in [1, 2, 8] {
            let proof = prove_tail_recursive_instance(&s, fib, &[n]).unwrap_or_else(|| panic!("fib({n}) should get an instance"));
            assert_eq!(proof.arity, 1);
            kernel::with_shift_cache(|| {
                kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.int_ty.clone(), proof.lhs.clone(), proof.rhs.clone()))
            })
            .expect("the recorded instance proof should independently re-typecheck");
        }
    }

    #[test]
    fn instance_visit_count_distinguishes_routine_samples_from_a_large_branching_one() {
        // Same fib shape as the test above. Naive Fibonacci's overlapping
        // subproblems mean the *memoized* visit count is linear in n
        // (0..=n, each visited once), not exponential -- confirmed
        // directly here, since that's the whole premise
        // `instance_from_scaffold`'s own threshold relies on: `jit.rs`'s
        // routine small samples (0, 1, 2, 3, -1, -3, ...) stay under it,
        // while a real instance like n=8 (this cache's own proven ~2x win)
        // clears it.
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

        let scaffold = build_universal(&s, fib).expect("fib should build a universal scaffold");
        let cap = 100;
        let count_at = |n_val: i64| instance_visit_count(&s, scaffold.self_call, &scaffold.leaves, &[n_val], cap);

        // n=0,1 hit the base case immediately (1 visit each); n=2 visits
        // {2,1,0}; n=8 visits {8,7,...,0} -- 9 distinct nodes, matching
        // n+1 exactly since every intermediate value is reached from
        // both f(n-1) and, one step later, f((n-1)-1).
        assert_eq!(count_at(0), 1);
        assert_eq!(count_at(1), 1);
        assert_eq!(count_at(2), 3);
        assert_eq!(count_at(8), 9);

        // Every sample jit.rs's own SAMPLE_ARGS routinely tries except
        // n=7/n=20 stays comfortably below the threshold that gates
        // `with_shift_cache` (6) -- confirming the routine, small-sample
        // path really does skip the cache, not just by coincidence.
        for small in [0, 1, 2, 3, -1, -3] {
            assert!(count_at(small) < 6, "n={small}: visit count {} should stay under the cache threshold", count_at(small));
        }
        for large in [7, 8, 20] {
            assert!(count_at(large) >= 6, "n={large}: visit count {} should cross the cache threshold", count_at(large));
        }

        // The `cap` is a real early-exit, not just an unused parameter:
        // a tiny cap must not let a large instance's count exceed it.
        assert_eq!(instance_visit_count(&s, scaffold.self_call, &scaffold.leaves, &[20], 3), 3);
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
        // inconsistent arities (1 then 2) at different call sites.
        // Unrelated to partial application of a *literal lambda* (see
        // a_partially_applied_literal_lambda_used_as_a_value_gets_a_closure_proof
        // below for that, now-covered, case): param_types_for declines to
        // classify an inconsistently-called parameter as `Clo`-typed at
        // all (mapping `ArityUse::Inconsistent` to `None`, exactly like
        // an absent entry), so `denote_closure`'s own purely-structural
        // classification -- which has no way to reason about a call
        // whose outcome depends on which concrete value `f` turns out to
        // be at runtime, not on term shape alone -- still can't make
        // sense of either call site here.
        //
        // `compile::try_compile` no longer agrees this is out of scope,
        // though: it now compiles this exact shape via a curried,
        // one-argument-at-a-time dispatch mechanism (see
        // `compile::tests::inconsistent_call_arity_for_a_parameter_now_compiles_via_curried_dispatch`
        // and the runnable capability tests alongside it). That's an
        // intentional, expected gap, not a regression -- extending
        // kernel-checked proof coverage to this new capability is
        // separately scoped future work (see `RELATED_WORK.md`'s own
        // notes on why it doesn't fit this file's existing, purely
        // structural methodology), not a byproduct of compile.rs alone
        // accepting more terms.
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
        kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
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
        kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
    fn a_whole_functions_result_being_a_closure_now_gets_a_closure_proof() {
        // \x. if x > 0 then inc else inc -- an `If` choosing between two
        // closures was already covered (denote_closure's own `Term::If`
        // via `ite_clo` -- see
        // a_closure_typed_ifs_own_result_used_as_a_value_gets_a_closure_proof
        // below), but `prove_closure_expr`'s own *top-level* call still
        // hardcoded `.int()?`, rejecting this term for an orthogonal
        // reason: `f`'s own body (the whole function's result) denotes as
        // `Clo`, not `Int`. Now that `Clo` is arity-indexed (`Clo_k`),
        // `prove_closure_expr` picks `result_ty` from `denote_closure`'s
        // own `Denoted` tag instead of assuming `Int` -- `Clo_1` here,
        // both `inc`s sharing arity 1 -- so this is now proven, not
        // rejected.
        let mut s = TermStore::new();
        let x = s.var(0);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, zero, x);
        let i1 = inc(&mut s);
        let i2 = inc(&mut s);
        let picked = s.if_(cond, i1, i2);
        let f = s.abs(picked);

        let proof = prove_closure_expr(&s, f).expect("a Clo-typed top-level result should now get a closure proof");
        assert_eq!(proof.arity, 1);
        kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
            .expect("the recorded proof should independently re-typecheck");
    }

    #[test]
    fn a_bare_closure_typed_parameter_read_gets_a_closure_proof() {
        // \f. if (f 0) then f else f -- `f`'s own arity is inferred as 1
        // only because `infer_closure_arities` needs *some* use-site call
        // to assign it one at all (see `TYPES.md` section 3.1's own
        // "Default" rule), supplied here by the condition `f 0` (its own
        // value otherwise unused); both branches then read `f` itself as
        // a bare value, exercising `Term::Var(i)`'s own `Denoted::Clo`
        // case as `prove_closure_expr`'s own top-level result -- the
        // simplest possible instance of the new capability.
        let mut s = TermStore::new();
        let f = s.var(0);
        let zero = s.lit(0);
        let cond = s.app(f, zero);
        let body = s.if_(cond, f, f);
        let h = s.abs(body);

        let proof = prove_closure_expr(&s, h).expect("a bare Clo-typed parameter read should get a closure proof");
        assert_eq!(proof.arity, 1);
        kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
            .expect("the recorded proof should independently re-typecheck");
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
            &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()),
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
                &kernel::id(alone_proof.result_ty.clone(), alone_proof.denotation.clone(), alone_proof.denotation.clone()),
            )
            .is_err(),
            "(twice inc) 5's proof should be rejected against twice-alone's type"
        );
    }

    /// Independently re-typechecks `proof` from scratch (not just
    /// trusting the `.ok()?` inside `prove_closure_expr_instance`) --
    /// the same discipline `tail_recursive_call_gets_a_relational_proof`
    /// already applies to `prove_tail_recursive_call`'s own per-instance
    /// proofs, which this function's own methodology mirrors.
    fn check_instance_proof(proof: &EquivalenceProof) {
        kernel::check(&proof.ctx, &proof.proof, &kernel::id(proof.result_ty.clone(), proof.denotation.clone(), proof.denotation.clone()))
            .expect("the recorded per-instance proof should independently re-typecheck");
    }

    #[test]
    fn prove_closure_expr_declines_where_the_instance_proof_picks_up() {
        // Same shape as compile.rs's
        // `an_inconsistently_called_parameter_matching_its_own_saturating_arity_agrees_with_the_interpreter`
        // -- documents exactly why the new strategy is needed: the
        // universal, structural proof still declines this shape (`f`'s
        // own inconsistent arity has no honest static type), even though
        // it's now perfectly provable per-instance.
        let mut s = TermStore::new();
        let a = s.var(1);
        let b = s.var(0);
        let add = s.prim(PrimOp::Add, a, b);
        let inner = s.abs(add);
        let f_lit = s.abs(inner);

        let f1 = s.var(0);
        let one1 = s.lit(1);
        let two1 = s.lit(2);
        let call_2 = s.app2(f1, one1, two1);
        let f2 = s.var(0);
        let one2 = s.lit(1);
        let call_1 = s.app(f2, one2);
        let zero = s.lit(0);
        let one_c = s.lit(1);
        let cond = s.prim(PrimOp::Lt, zero, one_c);
        let inner_body = s.if_(cond, call_2, call_1);
        let f_abs = s.abs(inner_body);
        let top = s.app(f_abs, f_lit);

        assert!(prove_closure_expr(&s, top).is_none());
        let proof = prove_closure_expr_instance(&s, top, &[]).expect("should be provable per-instance");
        assert_eq!(proof.arity, 0);
        check_instance_proof(&proof);
    }

    #[test]
    fn an_under_applying_instance_gets_a_per_instance_proof_too() {
        // compile.rs's
        // `an_inconsistently_called_parameter_matching_its_own_under_applying_arity_agrees_with_the_interpreter`.
        let mut s = TermStore::new();
        let a = s.var(0);
        let hundred = s.lit(100);
        let a_plus_100 = s.prim(PrimOp::Add, a, hundred);
        let f_lit = s.abs(a_plus_100);

        let f1 = s.var(0);
        let one1 = s.lit(1);
        let two1 = s.lit(2);
        let call_2 = s.app2(f1, one1, two1);
        let f2 = s.var(0);
        let one2 = s.lit(1);
        let call_1 = s.app(f2, one2);
        let one_c = s.lit(1);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Lt, one_c, zero); // always false
        let inner_body = s.if_(cond, call_2, call_1);
        let f_abs = s.abs(inner_body);
        let top = s.app(f_abs, f_lit);

        assert!(prove_closure_expr(&s, top).is_none());
        let proof = prove_closure_expr_instance(&s, top, &[]).expect("should be provable per-instance");
        check_instance_proof(&proof);
    }

    #[test]
    fn a_captured_value_reached_through_an_inlined_call_gets_a_per_instance_proof() {
        // compile.rs's
        // `a_capturing_closure_reached_through_an_inconsistently_called_parameter_agrees_with_the_interpreter`
        // -- exercises the two-frame fix directly: `f_lit`'s own capture
        // of `k` must resolve against `top`'s own (outer) frame, not
        // whatever frame is active once `f_abs`'s body is inlined.
        let mut s = TermStore::new();
        let k = s.var(2);
        let a = s.var(1);
        let b = s.var(0);
        let k_plus_a = s.prim(PrimOp::Add, k, a);
        let sum = s.prim(PrimOp::Add, k_plus_a, b);
        let inner = s.abs(sum);
        let f_lit = s.abs(inner);

        let f1 = s.var(0);
        let one1 = s.lit(1);
        let two1 = s.lit(2);
        let call_2 = s.app2(f1, one1, two1);
        let f2 = s.var(0);
        let one2 = s.lit(1);
        let call_1 = s.app(f2, one2);
        let zero = s.lit(0);
        let one_c = s.lit(1);
        let cond = s.prim(PrimOp::Lt, zero, one_c);
        let inner_body = s.if_(cond, call_2, call_1);
        let f_abs = s.abs(inner_body);
        let app = s.app(f_abs, f_lit);
        let top = s.abs(app);

        assert!(prove_closure_expr(&s, top).is_none());
        for k_val in [100i64, -7] {
            let proof = prove_closure_expr_instance(&s, top, &[k_val]).unwrap_or_else(|| panic!("k={k_val} should be provable per-instance"));
            check_instance_proof(&proof);
        }
    }

    #[test]
    fn a_runtime_chosen_literal_gets_a_per_instance_proof() {
        // compile.rs's
        // `a_parameters_own_value_arriving_via_an_if_between_two_literals_still_agrees_once_dispatched_generically`
        // -- the sharpest case: `f`'s own concrete identity isn't known
        // until `eval_dyn` concretely resolves the `If` choosing between
        // `add_lit`/`sub_lit`, *before* `f_abs`'s own body is even
        // reached.
        let mut s = TermStore::new();
        let a1 = s.var(1);
        let b1 = s.var(0);
        let add_body = s.prim(PrimOp::Add, a1, b1);
        let add_inner = s.abs(add_body);
        let add_lit = s.abs(add_inner);

        let a2 = s.var(1);
        let b2 = s.var(0);
        let sub_body = s.prim(PrimOp::Sub, a2, b2);
        let sub_inner = s.abs(sub_body);
        let sub_lit = s.abs(sub_inner);

        let pick = s.var(0);
        let zero_p = s.lit(0);
        let pick_cond = s.prim(PrimOp::Lt, zero_p, pick);
        let f_value = s.if_(pick_cond, add_lit, sub_lit);

        let f1 = s.var(0);
        let one1 = s.lit(1);
        let two1 = s.lit(2);
        let call_2 = s.app2(f1, one1, two1);
        let f2 = s.var(0);
        let one2 = s.lit(1);
        let call_1 = s.app(f2, one2);
        let zero_c = s.lit(0);
        let one_c = s.lit(1);
        let cond = s.prim(PrimOp::Lt, zero_c, one_c);
        let inner_body = s.if_(cond, call_2, call_1);
        let f_abs = s.abs(inner_body);
        let app = s.app(f_abs, f_value);
        let top = s.abs(app);

        assert!(prove_closure_expr(&s, top).is_none());
        for pick_val in [1i64, -1] {
            let proof = prove_closure_expr_instance(&s, top, &[pick_val]).unwrap_or_else(|| panic!("pick={pick_val} should be provable per-instance"));
            check_instance_proof(&proof);
        }
    }

    #[test]
    fn a_tail_recursive_loop_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof() {
        // Same shape as jit::tests::
        // a_tail_recursive_loop_compiles_and_is_kernel_verified_once_its_own_closure_parameter_turns_inconsistent
        // (and benches/common.rs's own
        // inconsistent_arity_loop_carried_parameter_loop): `rec f n g x =
        // if 1<0 then g(x,999) else (if n<=0 then x else f(n-1,g,g(x)))`,
        // `g` baked in as `inc = \y. y+1`. The dead `g(x,999)` call site
        // makes `param_types_for(it)` classify `g` as `Inconsistent` (->
        // `None`, same as an absent one) even though every call actually
        // taken passes it exactly one argument -- exactly the gap
        // `eval_dyn_direct_call` used to decline outright for a
        // `Rec`-wrapped root (`root_is_rec` check), and that
        // `eval_dyn_tail_recursive` now closes by following the loop's
        // own tail self-calls concretely instead of trying (and failing)
        // to classify `g` statically.
        let mut s = TermStore::new();
        let x_dead = s.var(0);
        let nine_ninety_nine = s.lit(999);
        let g_dead = s.var(1);
        let dead_call = s.app2(g_dead, x_dead, nine_ninety_nine);

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
        let live_body = s.if_(cond, x, rec_call);

        let one_c = s.lit(1);
        let zero_c = s.lit(0);
        let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
        let body = s.if_(dead_cond, dead_call, live_body);

        let g_binder = s.abs(body);
        let n_binder = s.abs(g_binder);
        let abs = s.abs(n_binder);
        let it = s.rec(abs);

        let y = s.var(0);
        let one2 = s.lit(1);
        let inc_body = s.prim(PrimOp::Add, y, one2);
        let inc = s.abs(inc_body);

        assert!(param_types_for(&s, it).unwrap().contains(&None));
        assert!(prove_closure_expr(&s, it).is_none(), "it itself has no fixed arity to prove universally over g's own slot");

        for n_val in [0i64, 1, 10] {
            let n_lit = s.lit(n_val);
            let x0 = s.lit(0);
            let partial = s.app2(it, n_lit, inc);
            let top = s.app(partial, x0);

            assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to it still can't be classified statically");
            let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
            check_instance_proof(&proof);
            assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), n_val, "n={n_val}: sanity check against the interpreter");
        }
    }

    #[test]
    fn a_loop_carried_call_result_that_itself_gates_termination_gets_a_per_instance_proof() {
        // rec f g x = if 1<0 then g(x,999) else (if x<=0 then x else
        // f(g, g(x))), `g` baked in as `dec = \y. y-1` -- unlike the test
        // just above (where the loop-carried call's own result, `g(x)`,
        // never itself influences which branch a later iteration takes,
        // only `n` does), here `g(x)`'s own concrete value is exactly
        // what the next iteration's own `x<=0` branches on. This is the
        // sharper regression guard `eval_dyn_tail_recursive`'s own
        // `eval_concrete_dyn` call needs: deliberately corrupting
        // `dyn_frame_to_env`'s own reversal (dropping its `.rev()`) is
        // *not* caught by the test above at all (nothing there ever reads
        // `x`'s own concrete numeral back), but *is* caught here, via the
        // sanity check against the interpreter below -- confirmed by
        // hand before trusting this test to mean anything.
        let mut s = TermStore::new();
        let x_dead = s.var(0);
        let nine_ninety_nine = s.lit(999);
        let g_dead = s.var(1);
        let dead_call = s.app2(g_dead, x_dead, nine_ninety_nine);

        let x = s.var(0);
        let g = s.var(1);
        let f = s.var(2);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, x, zero);
        let gx = s.app(g, x);
        let rec_call = s.app2(f, g, gx);
        let live_body = s.if_(cond, x, rec_call);

        let one_c = s.lit(1);
        let zero_c = s.lit(0);
        let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
        let body = s.if_(dead_cond, dead_call, live_body);

        let x_binder = s.abs(body);
        let g_binder = s.abs(x_binder);
        let it = s.rec(g_binder);

        let y = s.var(0);
        let one2 = s.lit(1);
        let dec_body = s.prim(PrimOp::Sub, y, one2);
        let dec = s.abs(dec_body);

        assert!(param_types_for(&s, it).unwrap().contains(&None));

        for x_val in [0i64, 1, 5] {
            let x0 = s.lit(x_val);
            let top = s.app2(it, dec, x0);

            let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("x={x_val} should be provable per-instance"));
            check_instance_proof(&proof);
            assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 0, "x={x_val}: sanity check against the interpreter");
        }
    }

    #[test]
    fn a_closure_argument_arriving_via_a_separate_saturated_call_that_itself_returns_a_clo_gets_a_per_instance_proof() {
        // `pick = \s. if s > 0 then add5 else sub5` (arity 1, its own
        // saturated call returns a further Clo_2 -- `combinator_return_type`
        // recognizes an `If` between two same-arity literal lambdas, same
        // as `denote_closure`'s own `ite_clo` case does structurally);
        // `f = \k. if 0<1 then k(1,2) else k(1)` (arity 1, `k` called at
        // two different arities -- `Inconsistent`, same trick as every
        // other per-instance test); `top = f(pick(3))`. `pick(3)`'s own
        // result never arrives as a bare literal lambda value the way
        // every other per-instance test's closure argument does -- it's
        // the result of a *separate* saturated call, so `eval_dyn_direct_call`
        // must inline *that* call too (previously declined outright via
        // its own `return_ty.is_some()` check) before `f`'s own
        // needs-inline logic even gets a `Clo` to work with at all.
        let mut s = TermStore::new();
        let a1 = s.var(1);
        let b1 = s.var(0);
        let add_body = s.prim(PrimOp::Add, a1, b1);
        let add_inner = s.abs(add_body);
        let add5 = s.abs(add_inner);

        let a2 = s.var(1);
        let b2 = s.var(0);
        let sub_body = s.prim(PrimOp::Sub, a2, b2);
        let sub_inner = s.abs(sub_body);
        let sub5 = s.abs(sub_inner);

        let s_var = s.var(0);
        let zero_p = s.lit(0);
        let pick_cond = s.prim(PrimOp::Lt, zero_p, s_var); // 0 < s, i.e. s > 0
        let pick_body = s.if_(pick_cond, add5, sub5);
        let pick = s.abs(pick_body);

        let k1 = s.var(0);
        let one_a = s.lit(1);
        let two_a = s.lit(2);
        let call2 = s.app2(k1, one_a, two_a);
        let k2 = s.var(0);
        let one_b = s.lit(1);
        let call1 = s.app(k2, one_b);
        let zero_c = s.lit(0);
        let one_c = s.lit(1);
        let f_cond = s.prim(PrimOp::Lt, zero_c, one_c); // 0 < 1, always true
        let f_body = s.if_(f_cond, call2, call1);
        let f = s.abs(f_body);

        assert!(param_types_for(&s, f).unwrap().contains(&None) && combinator_return_type(&s, pick).unwrap() == Some(2));

        for s_val in [3i64, -3] {
            let s_lit = s.lit(s_val);
            let pick_s = s.app(pick, s_lit);
            let top = s.app(f, pick_s);

            assert!(prove_closure_expr(&s, top).is_none(), "s={s_val}: f's own inconsistent k still can't be classified statically");
            let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("s={s_val} should be provable per-instance"));
            check_instance_proof(&proof);
            let expected = if s_val > 0 { 1 + 2 } else { 1 - 2 };
            assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), expected, "s={s_val}: sanity check against the interpreter");
        }
    }

    #[test]
    fn a_non_tail_self_call_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof() {
        // Same dead-call-site trick as the tail-recursive precedent
        // (`a_tail_recursive_loop_carrying_an_inconsistently_classified_closure_parameter_gets_a_per_instance_proof`
        // above), but the self-call now sits *inside* `1 + ..`, not in
        // tail position: `rec f n g x = if 1<0 then g(x,999) else (if
        // n<=0 then x else 1 + f(n-1,g,g(x)))`. `classify_step`'s own
        // `match_self_call` only recognizes a self-call that's the
        // *entire* remaining leaf, so this leaf -- `1 + f(...)` -- is a
        // `Base` case as far as `eval_dyn_tail_recursive`'s own loop is
        // concerned; the embedded self-call inside it is only reachable
        // via `eval_dyn`'s own new recognition, calling back into
        // `eval_dyn_tail_recursive` one Rust stack frame at a time.
        let mut s = TermStore::new();
        let x_dead = s.var(0);
        let nine_ninety_nine = s.lit(999);
        let g_dead = s.var(1);
        let dead_call = s.app2(g_dead, x_dead, nine_ninety_nine);

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
        let rec_call = s.app(f_n1_g, gx); // f(n-1, g, g(x))
        let one_addend = s.lit(1);
        let non_tail_call = s.prim(PrimOp::Add, one_addend, rec_call); // 1 + f(n-1,g,g(x))
        let live_body = s.if_(cond, x, non_tail_call);

        let one_c = s.lit(1);
        let zero_c = s.lit(0);
        let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
        let body = s.if_(dead_cond, dead_call, live_body);

        let g_binder = s.abs(body);
        let n_binder = s.abs(g_binder);
        let abs = s.abs(n_binder);
        let it = s.rec(abs);

        let y = s.var(0);
        let one2 = s.lit(1);
        let inc_body = s.prim(PrimOp::Add, y, one2);
        let inc = s.abs(inc_body);

        assert!(param_types_for(&s, it).unwrap().contains(&None));

        for n_val in [0i64, 1, 3, 10] {
            let n_lit = s.lit(n_val);
            let x0 = s.lit(0);
            let partial = s.app2(it, n_lit, inc);
            let top = s.app(partial, x0);

            assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to it still can't be classified statically");
            let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
            check_instance_proof(&proof);
            // x reaches n_val (one increment per level) by the time the
            // base case returns it, and "1 +" is added back once per
            // level on the way out -- n_val of each.
            assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), 2 * n_val, "n={n_val}: sanity check against the interpreter");
        }

        // Past `DynBudget::recursion_depth`'s own bound, this must
        // decline *cleanly* (a graceful `None`, the same "sound, not
        // complete" tolerance every other bounded search in this module
        // already has) rather than actually overflowing the native Rust
        // stack that many real embedded self-calls would otherwise
        // recurse through -- confirms the bound is a genuine safety net,
        // not just delaying a crash to a slightly deeper input.
        let deep_n = s.lit(1_000_000);
        let x0 = s.lit(0);
        let partial = s.app2(it, deep_n, inc);
        let top = s.app(partial, x0);
        assert!(
            prove_closure_expr_instance(&s, top, &[]).is_none(),
            "n=1_000_000 exceeds DynBudget::recursion_depth and should decline cleanly, not overflow the stack"
        );
    }

    #[test]
    fn branching_non_tail_self_calls_carrying_an_inconsistently_classified_closure_parameter_get_a_per_instance_proof() {
        // A genuinely *branching* non-tail shape (two self-calls in the
        // same leaf, Fibonacci-style), not just one embedded call:
        // `rec f n g = if 1<0 then g(0,999) else (if n<=1 then g(n) else
        // f(n-1,g) + f(n-2,g))`, `g` baked in as `inc = \y. y+1`. Each
        // occurrence of `f(..)` is just another embedded self-call as far
        // as `eval_dyn`'s own recognition is concerned -- this test
        // exists specifically to confirm that claim (from `eval_dyn`'s
        // own doc comment) holds for a real branching trace, not just a
        // single non-tail one.
        // Convention (matching every other per-instance test in this
        // module): the innermost binder is `Var(0)`, bound by whatever's
        // applied *last* -- `it.app2(n_lit, inc)` applies `n_lit` first,
        // `inc` last, so `g = Var(0)` (last-applied, innermost) and
        // `n = Var(1)` (first-applied, outermost); `f` (the self-
        // reference) sits at `Var(arity) = Var(2)`.
        let mut s = TermStore::new();
        let g_dead = s.var(0);
        let zero_dead = s.lit(0);
        let nine_ninety_nine = s.lit(999);
        let dead_call = s.app2(g_dead, zero_dead, nine_ninety_nine);

        let g_base = s.var(0);
        let n_base = s.var(1);
        let base_call = s.app(g_base, n_base); // g(n)

        let g1 = s.var(0);
        let n1 = s.var(1);
        let f1 = s.var(2);
        let one1 = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n1, one1);
        let call_n1 = s.app2(f1, n_minus_1, g1); // f(n-1, g)

        let g2 = s.var(0);
        let n2 = s.var(1);
        let f2 = s.var(2);
        let two2 = s.lit(2);
        let n_minus_2 = s.prim(PrimOp::Sub, n2, two2);
        let call_n2 = s.app2(f2, n_minus_2, g2); // f(n-2, g)

        let branch_sum = s.prim(PrimOp::Add, call_n1, call_n2);

        let n_cond = s.var(1);
        let one_c2 = s.lit(1);
        let cond = s.prim(PrimOp::Le, n_cond, one_c2); // n <= 1
        let live_body = s.if_(cond, base_call, branch_sum);

        let one_c = s.lit(1);
        let zero_c = s.lit(0);
        let dead_cond = s.prim(PrimOp::Lt, one_c, zero_c); // always false
        let body = s.if_(dead_cond, dead_call, live_body);

        let g_binder = s.abs(body); // innermost -- binds g (Var(0))
        let n_binder = s.abs(g_binder); // outermost -- binds n (Var(1))
        let it = s.rec(n_binder);

        let y = s.var(0);
        let one2 = s.lit(1);
        let inc_body = s.prim(PrimOp::Add, y, one2);
        let inc = s.abs(inc_body);

        assert!(param_types_for(&s, it).unwrap().contains(&None));

        for n_val in [0i64, 1, 2, 3, 4] {
            let n_lit = s.lit(n_val);
            let top = s.app2(it, n_lit, inc);

            assert!(prove_closure_expr(&s, top).is_none(), "n={n_val}: top's own call to it still can't be classified statically");
            let proof = prove_closure_expr_instance(&s, top, &[]).unwrap_or_else(|| panic!("n={n_val} should be provable per-instance"));
            check_instance_proof(&proof);
            // f(n) = inc(n) for n<=1, else f(n-1)+f(n-2) -- 1,2,3,5,8 for
            // n=0..4, hand-computed independently rather than derived
            // from the term itself, so this is a real cross-check.
            let expected = [1i64, 2, 3, 5, 8][n_val as usize];
            assert_eq!(eval::apply_term(&s, top, &[]).unwrap(), expected, "n={n_val}: sanity check against the interpreter");
        }
    }
}
