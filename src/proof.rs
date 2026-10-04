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
//! `build_node` and `eval.rs`'s `eval` recurse over the term in exactly
//! the same shape -- evaluate/compile the operands, then combine with the
//! same operator -- so `denote` (the single translation below) models both
//! readings, and the proof that they agree is `refl`. That's not a
//! shortcut: for straight-line, side-effect-free expressions, a stack-
//! machine compilation and a tree-walking interpretation provably compute
//! the same value by construction, and a kernel-checked `refl` is an
//! accurate, honest witness of exactly that fact -- no more, no less.
//!
//! ## Tail recursion: relational, per-execution proofs (`prove_tail_recursive_call`)
//!
//! `compile.rs` also turns *tail* self-recursion into a `loop`/`br`
//! (recursion -> iteration) -- the actually interesting transformation.
//! Checking a given transformed term borrows the *shape* of what real
//! verified compilers fall back to when full verification isn't
//! available -- validate the output of a compilation instead of proving
//! the compiler itself correct -- but lands one rung weaker than that,
//! and the distinction is worth stating plainly because the standard
//! term does **not** apply here:
//!
//! *Translation validation* (Pnueli et al.; Necula; Tristan & Leroy's
//! verified validators in CompCert) validates one **compilation**. The
//! checker runs once per compiled program, and when it succeeds the
//! compiled program is correct *for every input*. What
//! `prove_tail_recursive_call` validates is one **execution**: a single
//! concrete `(term, args)` trace, saying nothing whatever about any
//! other argument. That's a result-checking / certifying-computation
//! regime, not translation validation, and using the latter name for it
//! would claim precisely the all-inputs guarantee it lacks -- see
//! `jit::ProofStrength::Samples` and `RELATED_WORK.md` 28. tatic has no
//! per-compilation validator; the only all-inputs evidence it builds is
//! the universal theorem below.
//!
//! Mechanically, for a concrete `(term, args)`,
//! `prove_tail_recursive_call` follows the interpreter's own concrete trace
//! (which branch is taken at each unrolling, using the same shape
//! `build_node` classifies bodies with), and at each tail-call step,
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
//! may be an arbitrary tree of nested `If`s, matching what `build_node`
//! already accepts; each leaf may itself contain any number of self-call
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
//! have a direct comparison as its condition (`build_node`'s `If` arm in
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

use hashbrown::HashMap;
use std::rc::Rc;

use crate::compile::{self, Shape};
use crate::eval;
use crate::kernel::{self, Expr, Globals, Postulates};
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
    /// The prelude every proof starts from. `push` type-checks each entry
    /// (RELATED_WORK §69), which cost ~5 µs a proof when every proof
    /// rebuilt it, so it is built and checked once per thread and cloned:
    /// `globals` is an `im::Vector`, and the clone shares its nodes.
    pub fn new() -> Self {
        thread_local! { static PRELUDE: ArithPostulates = ArithPostulates::prelude(); }
        PRELUDE.with(Clone::clone)
    }

    fn prelude() -> Self {
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
    /// already exist. Scope parameters are `Free`s, and a push inside a
    /// scope adds a global, so `lit` may be called at any point.
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
    let all = |hs: &[Hash], out: &mut Vec<i64>| hs.iter().all(|&a| collect_literals(store, a, arity, self_idx, param_types, out));
    match compile::classify(store, h, arity, self_idx) {
        Shape::SelfCall(args) => all(&args, out),
        // Any other call only in the closures-aware fragment: through a
        // `Clo`-typed parameter at its own arity, or to a closure created
        // right here (see denote_closure_typed's own docs). Only the
        // arguments are ever collected from -- a combinator's own body is
        // never denoted regardless of whether it's called, matching
        // collect_literals_closure's identical "opaque, nothing to
        // collect" treatment of a bare Abs/Rec value.
        Shape::VarCall { var, args, .. } => {
            param_types.is_some_and(|pt| pt.get(var as usize).copied().flatten() == Some(args.len())) && all(&args, out)
        }
        Shape::CombinatorCall { args, .. } => param_types.is_some() && all(&args, out),
        Shape::OtherCall => false,
        Shape::Var(_) => true,
        Shape::Lit(n) => {
            if !out.contains(&n) {
                out.push(n);
            }
            true
        }
        Shape::Prim(_, a, b) => all(&[a, b], out),
        Shape::If(c, t, e) => all(&[c, t, e], out),
        // A freshly-created closure used as a bare value (not applied here
        // -- see denote_closure_typed's own docs), only when `param_types`
        // says we're in the closures-aware fragment at all (`None` means
        // the plain-arithmetic-only callers, `prove_pure_expr`/
        // `prove_tail_recursive_call`'s shared `setup`, where an `Abs`
        // anywhere is still unconditionally out of scope).
        Shape::Combinator { is_rec } => !is_rec && param_types.is_some(),
    }
}

/// Translates a `Var`/`Lit`/`Prim`/`If` term into a kernel `Int`
/// expression: `params[i]` stands for `Var(i)`, and every operator/literal
/// is read off `arith` (which must already have every literal postulated).
/// A shared subterm is denoted once and its denotation shared, so the
/// result is linear in the DAG (`RELATED_WORK.md` §48). That is exact:
/// the fragment has no binders, so a subterm's denotation depends only on
/// its hash.
fn denote(store: &TermStore, h: Hash, arith: &ArithPostulates, params: &[Expr]) -> Option<Expr> {
    denote_in(store, h, arith, params, &mut HashMap::new())
}

fn denote_in(
    store: &TermStore,
    h: Hash,
    arith: &ArithPostulates,
    params: &[Expr],
    memo: &mut HashMap<Hash, Expr>,
) -> Option<Expr> {
    if let Some(d) = memo.get(&h) {
        return Some(d.clone());
    }
    let d = match compile::classify(store, h, params.len(), None) {
        Shape::Var(i) => params.get(i as usize).cloned()?,
        Shape::Lit(n) => arith.lit_ref(n),
        Shape::Prim(op, a, b) => {
            let da = denote_in(store, a, arith, params, memo)?;
            let db = denote_in(store, b, arith, params, memo)?;
            kernel::app2(arith.op_ref(op), da, db)
        }
        Shape::If(c, t, e) => {
            let dc = denote_in(store, c, arith, params, memo)?;
            let dt = denote_in(store, t, arith, params, memo)?;
            let de = denote_in(store, e, arith, params, memo)?;
            kernel::app3(arith.ite_ref(), dc, dt, de)
        }
        Shape::SelfCall(_) | Shape::VarCall { .. } | Shape::CombinatorCall { .. } | Shape::OtherCall | Shape::Combinator { .. } => return None,
    };
    memo.insert(h, d.clone());
    Some(d)
}

/// A kernel-checked witness that a term's compiled and interpreted
/// readings agree: either for *every* input (`prove_pure_expr`, the
/// straight-line fragment) or for one specific call
/// (`prove_tail_recursive_call`, the tail-recursive fragment) -- both
/// always `Int`-typed, unlike `prove_closure_expr`'s own use of this same
/// struct, where `result_ty` may be `Int` or a `Clo_k` (a closure-typed
/// top-level result, e.g. `\x. \y. x+y` used bare).
pub struct EquivalenceProof {
    pub globals: Globals,
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
    arith.p.check(&proof, &proof_ty).ok()?;

    Some(EquivalenceProof {
        globals: arith.p.globals,
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


mod tail;
#[allow(unused_imports)]
pub use tail::*;
mod universal;
#[allow(unused_imports)]
pub use universal::*;
mod hardening;
#[allow(unused_imports)]
pub use hardening::*;
mod instance;
#[allow(unused_imports)]
pub use instance::*;
mod closures;
#[allow(unused_imports)]
pub use closures::*;
mod per_instance;
#[allow(unused_imports)]
pub use per_instance::*;

#[cfg(test)]
mod tests;
