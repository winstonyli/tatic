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

/// Walks `h` (a `build_node`-shaped If-chain, in tail position) using
/// concrete params to decide which branch is taken, mirroring
/// `compile::build_node`'s own structure exactly: an `If`'s condition is
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
    match compile::classify(store, h, arity, Some(self_idx)) {
        Shape::If(c, t, e) => {
            let cv = eval_concrete(store, c, concrete)?;
            classify_step(store, if cv != 0 { t } else { e }, arity, self_idx, concrete)
        }
        Shape::SelfCall(args) => Some(StepOutcome::TailCall(args)),
        _ => Some(StepOutcome::Base(h)),
    }
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
    // A cost bound, shared with the closure-capable sibling of this loop
    // -- see `DynBudget::new` for why it is 200 and what that was sized
    // against.
    const MAX_STEPS: usize = 200;

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
fn apply_n(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, kernel::app)
}

/// `Ev(params, v) : Sort(0)` -- `ev_pos`'s postulate (see `build_universal`)
/// applied to `params` then `v`, via `arith.p.get`. A free function (not
/// just `build_universal`'s own local closure) so `build_ev_witness`'s
/// branching-leaf recasting can build the same `Ev(...)` application it
/// does, rather than reimplementing it.
fn ev_of(arith: &ArithPostulates, ev_pos: usize, params: &[Expr], v: Expr) -> Expr {
    apply_n(arith.p.get(ev_pos), params.iter().cloned().chain([v]))
}

// --- hardening against composition bugs -----------------------------------
//
// A function composing an `Expr` from more than one recursive sub-call can
// still make a composition mistake, even though a pushed `Const` shifts
// nothing (`RELATED_WORK.md` §68, §69).
//
// This helper turns any such mistake into an immediate, precisely located
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
fn debug_assert_has_type(p: &Postulates, e: &Expr, expected: &Expr, label: &str) {
    if let Err(err) = p.check_open(e, expected) {
        panic!(
            "composition bug in {label}: the value doesn't have its expected type.\n  \
             error: {err}\n  value: {e:?}\n  expected type: {expected:?}"
        );
    }
}
#[cfg(not(debug_assertions))]
fn debug_assert_has_type(_p: &Postulates, _e: &Expr, _expected: &Expr, _label: &str) {}

/// `combine`'s value at `params`/`ihs` (both hoisted to a free function --
/// not just a closure local to `prove_tail_recursive_universal` -- so
/// `build_ev_witness` can reuse it too).
fn combine_of(combine: &Expr, params: &[Expr], ihs: &[Expr]) -> Expr {
    apply_n(combine.clone(), params.iter().cloned().chain(ihs.iter().cloned()))
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
/// `denote_with_placeholders` the same way a `Prim` is.
#[derive(Clone)]
enum DecisionTree {
    If { cond: Hash, then_branch: Box<DecisionTree>, else_branch: Box<DecisionTree> },
    Leaf(Hash),
}

/// Classifies `h` into a [`DecisionTree`]. Every `If`'s condition must be
/// a direct comparison (same restriction `build_node`'s `If` arm in `compile.rs`
/// already imposes, and what lets `cond_premise` below use plain `Id`
/// equality -- a comparison only ever denotes to `0` or `1`).
fn classify_tree(store: &TermStore, h: Hash) -> Option<DecisionTree> {
    if let Term::If(c, t, e) = store.resolve(h) {
        let (c, t, e) = (*c, *t, *e);
        if !matches!(store.resolve(c), Term::Prim(op, _, _) if compile::is_comparison(*op)) {
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
    let all = |hs: &[Hash], out: &mut Vec<Vec<Hash>>| hs.iter().all(|&a| find_self_calls(store, a, self_call, param_types, out));
    match compile::classify(store, h, self_call.arity, Some(self_call.idx)) {
        Shape::SelfCall(args) => {
            out.push(args);
            true
        }
        Shape::VarCall { var, args, .. } => param_types.get(var as usize).copied().flatten() == Some(args.len()) && all(&args, out),
        // A closure created and (fully or partially) called right here --
        // see `denote_with_placeholders`'s own docs. Recurses into the
        // arguments only, never into the combinator's own body: a genuine
        // self-call occurring *inside* a nested closure's body would need
        // `self_call.idx` shifted by that closure's own arity to still
        // refer to the same absolute position, which
        // `compile::match_self_call`'s unadjusted check can't see -- the
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
        // `denote_with_placeholders`'s matching arm): recurse into all
        // three the same way `Prim` does, so a self-call inside either
        // branch is still found, in the same left-to-right, depth-first
        // order `denote_with_placeholders` will later walk.
        Shape::If(c, t, e) => all(&[c, t, e], out),
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
/// alike. `params` are the scope's bound parameters, as for
/// `denote_closure_typed`.
#[allow(clippy::too_many_arguments)]
fn denote_with_placeholders(
    store: &TermStore,
    h: Hash,
    self_call: SelfCall,
    param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[Expr],
    placeholders: &[Expr],
    next: &mut usize,
) -> Option<Denoted> {
    match compile::classify(store, h, self_call.arity, Some(self_call.idx)) {
        Shape::SelfCall(_) => {
            let v = placeholders.get(*next).cloned();
            *next += 1;
            v.map(Denoted::Int)
        }
        shape @ (Shape::VarCall { .. } | Shape::CombinatorCall { .. }) => match app_shape(store, shape, param_types)? {
            AppShape::ParamCall { root, k, args } => {
                let callee = denote_with_placeholders(store, root, self_call, param_types, combinators, params, placeholders, next)?.clo()?;
                let mut arg_exprs = Vec::with_capacity(k);
                for &a in &args {
                    let e = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?.int()?;
                    arg_exprs.push(e);
                }
                let applied = apply_n(callee, arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_with_placeholders: call_indirect application");
                Some(Denoted::Int(applied))
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
                let env_expr = if root_captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &root_captures, params, param_types)?;
                    Some(e)
                };
                let mut arg_exprs = Vec::with_capacity(k);
                for (j, &a) in args.iter().enumerate() {
                    let d = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?;
                    let e = arg_denotation(d, callee_param_types[arity - 1 - j], || return_type_of(store, a, self_call.arity, Some(self_call.idx), param_types))?;
                    arg_exprs.push(e);
                }
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.clone());
                }
                all_args.extend(arg_exprs.iter().cloned());
                let applied = apply_n(pap_fn, all_args);
                let clo_ty = combinators.cp.clo_ty(arity - k + pap_extra_arity(store, root));
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_with_placeholders: partial application");
                Some(Denoted::Clo(applied))
            }
            AppShape::LitLambdaExact { root, args, callee_param_types } | AppShape::LitLambdaOver { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
                let sat_args = &args[..arity];
                let (c_arity, c_body, c_is_rec) = compile::peel(store, root)?;
                let captures = compile::free_vars(store, c_body, c_arity, c_is_rec);
                let call_fn = combinators.call_ref(root, &captures, param_types)?;
                let env_expr = if captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &captures, params, param_types)?;
                    Some(e)
                };
                let mut arg_exprs = Vec::with_capacity(arity);
                for (j, &a) in sat_args.iter().enumerate() {
                    let d = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?;
                    let e = arg_denotation(d, callee_param_types[arity - 1 - j], || return_type_of(store, a, self_call.arity, Some(self_call.idx), param_types))?;
                    arg_exprs.push(e);
                }
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.clone());
                }
                all_args.extend(arg_exprs.iter().cloned());
                let sat_applied = apply_n(call_fn, all_args);
                let return_ty = combinator_return_type(store, root).unwrap_or(None);
                let returns_clo = return_ty.is_some();
                let sat_ty = match return_ty {
                    Some(k) => combinators.cp.clo_ty(k),
                    None => combinators.cp.arith.int_ty(),
                };
                debug_assert_has_type(&combinators.cp.arith.p, &sat_applied, &sat_ty, "denote_with_placeholders: direct combinator call");

                if args.len() == arity {
                    return Some(if returns_clo { Denoted::Clo(sat_applied) } else { Denoted::Int(sat_applied) });
                }

                if !returns_clo {
                    return None; // over-application of a plain Int result: genuinely out of scope
                }
                let extra_args = &args[arity..];
                let mut extra_arg_exprs = Vec::with_capacity(extra_args.len());
                for &a in extra_args {
                    let e = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?.int()?;
                    extra_arg_exprs.push(e);
                }
                let applied = apply_n(sat_applied, extra_arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_with_placeholders: over-application dispatch");
                Some(Denoted::Int(applied))
            }
        },
        Shape::OtherCall => None,
        Shape::Var(i) => {
            let i = i as usize;
            let p = params.get(i)?.clone();
            match *param_types.get(i)? {
                Some(_) => Some(Denoted::Clo(p)),
                None => Some(Denoted::Int(p)),
            }
        }
        Shape::Lit(n) => Some(Denoted::Int(combinators.cp.arith.lit_ref(n))),
        Shape::Prim(op, a, b) => {
            let da = denote_with_placeholders(store, a, self_call, param_types, combinators, params, placeholders, next)?.int()?;
            let db = denote_with_placeholders(store, b, self_call, param_types, combinators, params, placeholders, next)?.int()?;
            let op_ref = combinators.cp.arith.op_ref(op);
            let applied = kernel::app2(op_ref, da, db);
            let int_ty = combinators.cp.arith.int_ty();
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_with_placeholders: Prim");
            Some(Denoted::Int(applied))
        }
        // A freshly-created closure *value*, not (yet) called -- mirrors
        // `denote_closure`'s own value-leaf `Term::Abs | Term::Rec` case.
        Shape::Combinator { is_rec: false } => {
            let (arity, body, is_rec) = compile::peel(store, h)?;
            if arity == 0 {
                return None;
            }
            let captures = compile::free_vars(store, body, arity, is_rec);
            let sym = combinators.register(h, &captures, param_types)?;
            if captures.is_empty() {
                return Some(Denoted::Clo(sym));
            }
            let env = build_env_expr(combinators, &captures, params, param_types)?;
            let applied = kernel::app(sym, env);
            let clo_ty = combinators.cp.clo_ty(arity);
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_with_placeholders: capturing closure value");
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
        Shape::If(c, t, e) => {
            let dc = denote_with_placeholders(store, c, self_call, param_types, combinators, params, placeholders, next)?.int()?;
            let dt = denote_with_placeholders(store, t, self_call, param_types, combinators, params, placeholders, next)?;
            let dt_is_clo = matches!(dt, Denoted::Clo(_));
            let dt = match dt {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            };
            let de = denote_with_placeholders(store, e, self_call, param_types, combinators, params, placeholders, next)?;
            let de_is_clo = matches!(de, Denoted::Clo(_));
            let de = match de {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            };
            match (dt_is_clo, de_is_clo) {
                (false, false) => {
                    let ite = combinators.cp.arith.ite_ref();
                    let applied = kernel::app3(ite, dc, dt, de);
                    let int_ty = combinators.cp.arith.int_ty();
                    debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_with_placeholders: nested If (Int branches)");
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
                    let t_arity = return_type_of(store, t, self_call.arity, Some(self_call.idx), param_types).flatten()?;
                    let e_arity = return_type_of(store, e, self_call.arity, Some(self_call.idx), param_types).flatten()?;
                    if t_arity != e_arity {
                        return None;
                    }
                    let ite_clo = combinators.cp.ite_clo_ref(t_arity);
                    let applied = kernel::app3(ite_clo, dc, dt, de);
                    let clo_ty = combinators.cp.clo_ty(t_arity);
                    debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_with_placeholders: nested If (Clo branches)");
                    Some(Denoted::Clo(applied))
                }
                _ => None,
            }
        }
        Shape::Combinator { .. } => None, // a bare `Term::Rec` is out of scope when there is a self-call,
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
/// `params` are the enclosing scope's bound parameters, which no push
/// shifts. `register`/`call_ref`/`pap_ref` each may push a
/// postulate on first use. A bare `Term::Rec` (a
/// self-recursive combinator *nested* inside another one's body) stays
/// out of scope, unlike `denote_closure`'s own fragment -- proving one induction correct while assuming another is a genuinely
/// different, unexplored problem, not attempted here.
fn denote_closure_typed(
    store: &TermStore,
    h: Hash,
    self_call: Option<SelfCall>,
    param_types: &[Option<usize>],
    combinators: &mut ClosureCombinators<'_>,
    params: &[Expr],
) -> Option<Denoted> {
    // with a self-call: its arity and index; without one (`denote_closure`), the function's own parameter counts and no index
    let (classify_arity, classify_idx, ret_arity, ret_idx) = match self_call {
        Some(sc) => (sc.arity, Some(sc.idx), sc.arity, Some(sc.idx)),
        None => (params.len(), None, param_types.len(), None),
    };
    match compile::classify(store, h, classify_arity, classify_idx) {
        // Never substituted here -- see this function's own docs.
        Shape::SelfCall(_) => None,
        shape @ (Shape::VarCall { .. } | Shape::CombinatorCall { .. }) => match app_shape(store, shape, param_types)? {
            AppShape::ParamCall { root, k, args } => {
                let callee = denote_closure_typed(store, root, self_call, param_types, combinators, params)?.clo()?;
                let mut arg_exprs = Vec::with_capacity(k);
                for &a in &args {
                    let e = denote_closure_typed(store, a, self_call, param_types, combinators, params)?.int()?;
                    arg_exprs.push(e);
                }
                let applied = apply_n(callee, arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure_typed: call_indirect application");
                Some(Denoted::Int(applied))
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
                let env_expr = if root_captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &root_captures, params, param_types)?;
                    Some(e)
                };
                let mut arg_exprs = Vec::with_capacity(k);
                for (j, &a) in args.iter().enumerate() {
                    let d = denote_closure_typed(store, a, self_call, param_types, combinators, params)?;
                    let e = arg_denotation(d, callee_param_types[arity - 1 - j], || return_type_of(store, a, ret_arity, ret_idx, param_types))?;
                    arg_exprs.push(e);
                }
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.clone());
                }
                all_args.extend(arg_exprs.iter().cloned());
                let applied = apply_n(pap_fn, all_args);
                let clo_ty = combinators.cp.clo_ty(arity - k + pap_extra_arity(store, root));
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_closure_typed: partial application");
                Some(Denoted::Clo(applied))
            }
            AppShape::LitLambdaExact { root, args, callee_param_types } | AppShape::LitLambdaOver { root, args, callee_param_types } => {
                let arity = callee_param_types.len();
                let sat_args = &args[..arity];
                let (c_arity, c_body, c_is_rec) = compile::peel(store, root)?;
                let captures = compile::free_vars(store, c_body, c_arity, c_is_rec);
                let call_fn = combinators.call_ref(root, &captures, param_types)?;
                let env_expr = if captures.is_empty() {
                    None
                } else {
                    let e = build_env_expr(combinators, &captures, params, param_types)?;
                    Some(e)
                };
                let mut arg_exprs = Vec::with_capacity(arity);
                for (j, &a) in sat_args.iter().enumerate() {
                    let d = denote_closure_typed(store, a, self_call, param_types, combinators, params)?;
                    let e = arg_denotation(d, callee_param_types[arity - 1 - j], || return_type_of(store, a, ret_arity, ret_idx, param_types))?;
                    arg_exprs.push(e);
                }
                let mut all_args = Vec::with_capacity(1 + arg_exprs.len());
                if let Some(env_expr) = &env_expr {
                    all_args.push(env_expr.clone());
                }
                all_args.extend(arg_exprs.iter().cloned());
                let sat_applied = apply_n(call_fn, all_args);
                let return_ty = combinator_return_type(store, root).unwrap_or(None);
                let returns_clo = return_ty.is_some();
                let sat_ty = match return_ty {
                    Some(k) => combinators.cp.clo_ty(k),
                    None => combinators.cp.arith.int_ty(),
                };
                debug_assert_has_type(&combinators.cp.arith.p, &sat_applied, &sat_ty, "denote_closure_typed: direct combinator call");

                if args.len() == arity {
                    return Some(if returns_clo { Denoted::Clo(sat_applied) } else { Denoted::Int(sat_applied) });
                }

                if !returns_clo {
                    return None; // over-application of a plain Int result: genuinely out of scope
                }
                let extra_args = &args[arity..];
                let mut extra_arg_exprs = Vec::with_capacity(extra_args.len());
                for &a in extra_args {
                    let e = denote_closure_typed(store, a, self_call, param_types, combinators, params)?.int()?;
                    extra_arg_exprs.push(e);
                }
                let applied = apply_n(sat_applied, extra_arg_exprs);
                let int_ty = combinators.cp.arith.int_ty();
                debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure_typed: over-application dispatch");
                Some(Denoted::Int(applied))
            }
        },
        Shape::OtherCall => None,
        Shape::Var(i) => {
            let i = i as usize;
            let p = params.get(i)?.clone();
            match *param_types.get(i)? {
                Some(_) => Some(Denoted::Clo(p)),
                None => Some(Denoted::Int(p)),
            }
        }
        Shape::Lit(n) => Some(Denoted::Int(combinators.cp.arith.lit_ref(n))),
        Shape::Prim(op, a, b) => {
            let da = denote_closure_typed(store, a, self_call, param_types, combinators, params)?.int()?;
            let db = denote_closure_typed(store, b, self_call, param_types, combinators, params)?.int()?;
            let op_ref = combinators.cp.arith.op_ref(op);
            let applied = kernel::app2(op_ref, da, db);
            let int_ty = combinators.cp.arith.int_ty();
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure_typed: Prim");
            Some(Denoted::Int(applied))
        }
        // Mirrors `denote_closure`'s identical three-way match: both
        // branches `Int` via `ite_ref`, both `Clo` via `ite_clo_ref`
        // (e.g. a self-call argument `f(n-1, if c then g else h)`,
        // choosing which `Clo`-typed value to thread onward), a mismatch
        // rejected.
        Shape::If(c, t, e) => {
            let dc = denote_closure_typed(store, c, self_call, param_types, combinators, params)?.int()?;
            let dt = denote_closure_typed(store, t, self_call, param_types, combinators, params)?;
            let dt_is_clo = matches!(dt, Denoted::Clo(_));
            let dt = match dt {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            };
            let de = denote_closure_typed(store, e, self_call, param_types, combinators, params)?;
            let de_is_clo = matches!(de, Denoted::Clo(_));
            let de = match de {
                Denoted::Int(e) | Denoted::Clo(e) => e,
            };
            match (dt_is_clo, de_is_clo) {
                (false, false) => {
                    let ite = combinators.cp.arith.ite_ref();
                    let applied = kernel::app3(ite, dc, dt, de);
                    let int_ty = combinators.cp.arith.int_ty();
                    debug_assert_has_type(&combinators.cp.arith.p, &applied, &int_ty, "denote_closure_typed: If (Int branches)");
                    Some(Denoted::Int(applied))
                }
                (true, true) => {
                    // See `denote_with_placeholders`'s identical case for
                    // why `return_type_of` (not `Denoted::Clo` itself) is
                    // the source of the shared arity here.
                    let t_arity = return_type_of(store, t, ret_arity, ret_idx, param_types).flatten()?;
                    let e_arity = return_type_of(store, e, ret_arity, ret_idx, param_types).flatten()?;
                    if t_arity != e_arity {
                        return None;
                    }
                    let ite_clo = combinators.cp.ite_clo_ref(t_arity);
                    let applied = kernel::app3(ite_clo, dc, dt, de);
                    let clo_ty = combinators.cp.clo_ty(t_arity);
                    debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_closure_typed: If (Clo branches)");
                    Some(Denoted::Clo(applied))
                }
                _ => None,
            }
        }
        // A freshly-created closure *value*, not (yet) called -- e.g.
        // threaded onward as the next iteration's own closure-typed
        // parameter, `f(n-1, \y. acc+y)`. Mirrors `denote_closure`'s own
        // value-leaf `Term::Abs | Term::Rec` case exactly.
        Shape::Combinator { is_rec } if !(is_rec && self_call.is_some()) => {
            let (arity, body, is_rec) = compile::peel(store, h)?;
            if arity == 0 {
                return None;
            }
            let captures = compile::free_vars(store, body, arity, is_rec);
            let sym = combinators.register(h, &captures, param_types)?;
            if captures.is_empty() {
                return Some(Denoted::Clo(sym));
            }
            let env = build_env_expr(combinators, &captures, params, param_types)?;
            let applied = kernel::app(sym, env);
            let clo_ty = combinators.cp.clo_ty(arity);
            debug_assert_has_type(&combinators.cp.arith.p, &applied, &clo_ty, "denote_closure_typed: capturing closure value");
            Some(Denoted::Clo(applied))
        }
        Shape::Combinator { .. } => None, // a bare `Term::Rec` is out of scope when there is a self-call,
    }
}

/// Binds `n` fresh `Int`-typed parameters in a new scope, lets `build`
/// bind more of its own and construct a body term, then closes
/// *everything* bound since entry (the `n` params plus anything `build`
/// itself bound, e.g. `v` or `e`) into nested binders around that body,
/// rolling them back afterward. Pass `kernel::Binder::Pi` to build a
/// *type* (quantifying over these params) or `kernel::Binder::Lam` to build a *value* of that
/// type (e.g. a motive or a proof to pass as an argument) -- getting this
/// wrong is a real, easy-to-make mistake (a `Pi` where a `Lam` was
/// needed), not a hypothetical one.
fn params_and_close(
    arith: &mut ArithPostulates,
    n: usize,
    binder: kernel::Binder,
    build: impl FnOnce(&mut ArithPostulates, &[Expr]) -> Option<Expr>,
) -> Option<Expr> {
    let s = arith.p.open();
    let params: Vec<Expr> = (0..n)
        .map(|_| {
            let ty = arith.int_ty();
            arith.p.bind(ty)
        })
        .collect();
    match build(arith, &params) {
        Some(b) => Some(arith.p.close(s, binder, b)),
        None => {
            arith.p.abandon(s);
            None
        }
    }
}

/// Like [`params_and_close`], but for `build_universal`'s own closure-aware
/// pipeline: binds one fresh parameter per entry of `param_types`, typed
/// `Clo_k` or `Int` to match, so `build`'s own params may be mixed-typed.
fn params_and_close_typed(
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
/// compiled code's own recursive structure (`loop_val`) reconstructs from
/// that witness -- covers tail recursion and general (non-tail) recursion
/// alike (see module docs).
pub struct UniversalTailProof {
    pub globals: Globals,
    pub arity: usize,
    /// `: Pi p_0..p_{arity-1} v (e : Ev(p_0,..,v)). Id(Int, loop_val(..,e), v)`.
    pub theorem_ty: Expr,
    pub theorem_proof: Expr,
}

/// Everything `prove_tail_recursive_universal`'s theorem was built from,
/// kept around (instead of dropped) so `prove_tail_recursive_instance` can
/// reuse it to build a concrete `Ev`-witness afterward, without redoing any
/// of the theorem's own construction. Witness-building pushes further
/// postulates onto `arith.p.globals` (fresh literal constants,
/// `assume_prim_fact` axioms) after this scaffold is built.
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
    combines: Vec<Expr>,
    ev_leaf_positions: Vec<usize>,
    /// `Ev`'s own postulate position (see `build_universal`) -- needed by
    /// `build_ev_witness`'s branching-leaf recasting, which builds `Ev(...)`
    /// applications directly rather than through a leaf-specific constructor.
    ev_pos: usize,
    theorem_ty: Expr,
    theorem_proof: Expr,
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
    // `prove_tail_recursive_call`'s convention exactly) -- closure-aware
    // via `denote_closure_typed` (a loop-carried `Clo`-typed argument, or a
    // plain `Int` one possibly computed by calling one), each checked
    // against `param_types[i]`, the *target* slot's own type.
    let new_params_for = |arith: &mut ClosureCombinators<'_>, call_args: &[Hash], params: &[Expr]| -> Option<Vec<Expr>> {
        (0..arity)
            .map(|i| {
                let d = denote_closure_typed(store, call_args[arity - 1 - i], Some(self_call), &param_types, arith, params)?;
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
            ty = kernel::arrow(dom.clone(), ty);
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
            let ev_np = ev_of(arith, &np, v.clone());
            es.push(arith.p.bind(ev_np));
        }
        Some((vs, es))
    };

    // combine_i : Pi params. Pi ih_1:Int .. ih_{k_i}:Int. Int -- leaf i's
    // own arithmetic expression with each self-call occurrence replaced
    // by the corresponding `ih_j` (`denote_with_placeholders`), closed
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
                denote_with_placeholders(store, leaf.expr, self_call, &param_types, arith, pp, pp2, &mut 0)?.int()
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
        apply_n(p_ref.clone(), params.iter().cloned().chain([v, e]))
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
                ih_tys.push(p_of(arith, &np, v.clone(), e.clone()));
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
        // out of `build_universal`, leaving `p_scope` (and `P`) open.
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
        let ev_pv = ev_of(arith, pp, v.clone());
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

    let ev_rec_ty_body = leaf_case_tys.iter().rev().fold(concl_ty, |acc, ty| kernel::arrow(ty.clone(), acc));
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
        ev_rec_ref(arith, const_int_motive.clone(), &loop_leaves, params, v, e)
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
                recursive_vals.push(loop_val(arith, &np, v.clone(), e.clone()));
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
        let ev_pv = ev_of(arith, pp, v.clone());
        let e = arith.p.bind(ev_pv);
        Some(kernel::id(arith.int_ty(), loop_val(arith, pp, v.clone(), e), v))
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
                let ih_ty = kernel::id(arith.int_ty(), loop_val(arith, &np, v.clone(), e.clone()), v.clone());
                ihs.push(arith.p.bind(ih_ty));
            }

            let mut recursive_vals = Vec::with_capacity(leaf.calls.len());
            for ((call, v), e) in leaf.calls.iter().zip(&vs).zip(&es) {
                let np = new_params_for(arith, call, pp)?;
                recursive_vals.push(loop_val(arith, &np, v.clone(), e.clone()));
            }

            let eb = apply_n(
                arith.p.get(ev_leaf_pos),
                pp.iter().cloned().chain(premises.iter().cloned()).chain(vs.iter().cloned()).chain(es.iter().cloned()),
            );
            let step_eq = apply_n(
                arith.p.get(loop_val_leaf_eq_pos),
                pp.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es),
            );
            let f_partial = apply_n(combine.clone(), pp.iter().cloned());
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
        let ev_pv = ev_of(arith, pp, v.clone());
        let e = arith.p.bind(ev_pv);
        Some(kernel::id(arith.int_ty(), loop_val(arith, pp, v.clone(), e), v))
    })?;

    let theorem_proof = params_and_close_typed(&mut arith, &param_types, kernel::Binder::Lam, |arith, pp| {
        let v = { let ty = arith.int_ty(); arith.p.bind(ty) };
        let ev_pv = ev_of(arith, pp, v.clone());
        let e = arith.p.bind(ev_pv);
        Some(ev_rec_ref(arith, id_motive.clone(), &theorem_leaves, pp, v, e))
    })?;

    arith.p.check(&theorem_proof, &theorem_ty).ok()?;

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
/// recursion or called via ordinary application (`Clo_k` is a literal
/// Pi type, not an opaque postulate -- see `ClosurePostulates::clo_ty`),
/// is covered; so is a closure
/// genuinely created and (fully or partially) called anywhere in the body
/// -- a self-call argument (`f(n-1, (\y. acc+y)(n))`) or a leaf's own
/// top-level expression (`(\y. n+y)(5) + f(n-1)`) alike (see module
/// docs). A leaf may itself contain a further nested `If`, purely
/// arithmetic or choosing between two `Clo`-typed values.
pub fn prove_tail_recursive_universal(store: &TermStore, h: Hash) -> Option<UniversalTailProof> {
    let scaffold = build_universal(store, h)?;
    let theorem_ty = scaffold.theorem_ty.clone();
    let theorem_proof = scaffold.theorem_proof.clone();
    Some(UniversalTailProof {
        globals: scaffold.combinators.cp.arith.p.globals,
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
/// `params`/`param_facts`, and every intermediate value this function
/// builds, need no anchoring: a postulate is a `Const` and a scope
/// parameter is a `Free` (`RELATED_WORK.md` §§69-70), so `assume_prim_fact`
/// (and recursing into a sibling sub-expression) pushing further postulates
/// onto `arith.p.globals` never shifts a value already resolved here.
fn eval_and_prove(
    store: &TermStore,
    h: Hash,
    combinators: &mut ClosureCombinators<'_>,
    params: &[Expr],
    concrete: &[i64],
    param_facts: &[Expr],
) -> Option<(i64, Expr, Expr)> {
    match compile::classify(store, h, params.len(), None) {
        // `param_types` is always empty here: every caller of this
        // function (via `instance_from_scaffold`'s own precondition) only
        // ever runs where the *outer* frame is entirely `Int`-typed, so
        // `AppShape::ParamCall` can never legitimately classify -- passing
        // `&[]` makes `app_shape`'s own `VarCall` case fail cleanly (an
        // out-of-range lookup), the same as an explicit all-`None` array
        // would, without needing to fabricate one.
        shape @ (Shape::VarCall { .. } | Shape::CombinatorCall { .. }) => match app_shape(store, shape, &[])? {
            AppShape::LitLambdaExact { root, args, callee_param_types } => {
                eval_and_prove_call(store, root, &args, &callee_param_types, combinators, params, concrete, param_facts)
            }
            // `root`'s own saturated call returns a `Clo_k`, then the
            // extra arguments are dispatched against it directly -- see
            // `eval_and_prove_call_over`'s own docs.
            AppShape::LitLambdaOver { root, args, callee_param_types } => {
                eval_and_prove_call_over(store, root, &args, &callee_param_types, combinators, params, concrete, param_facts)
            }
            // A `Clo`-typed result (`LitLambdaPartial`) has no concrete
            // representation at all (see `instance_from_scaffold`'s own
            // docs); `ParamCall` is structurally unreachable (see above).
            AppShape::ParamCall { .. } | AppShape::LitLambdaPartial { .. } => None,
        },
        Shape::Var(i) => {
            let i = i as usize;
            Some((*concrete.get(i)?, params.get(i)?.clone(), param_facts.get(i)?.clone()))
        }
        Shape::Lit(n) => {
            let l = combinators.cp.arith.lit_ref(n);
            Some((n, l.clone(), kernel::refl(l)))
        }
        Shape::Prim(op, a, b) => {
            let (xa, da, pa) = eval_and_prove(store, a, combinators, params, concrete, param_facts)?;
            let (xb, db, pb) = eval_and_prove(store, b, combinators, params, concrete, param_facts)?;
            let fact = combinators.cp.arith.assume_prim_fact(op, xa, xb);
            let result = apply_prim_concrete(op, xa, xb);

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
            debug_assert_has_type(&combinators.cp.arith.p, &proof, &kernel::id(int_ty, lhs.clone(), rhs), "eval_and_prove: Prim proof");
            Some((result, lhs, proof))
        }
        // Mirrors the `Prim` case just above, via `assume_ite_fact`
        // instead of `assume_prim_fact`: `denote`/`ite_ref` embeds an `If`
        // as fully opaque (both branches always denoted, never
        // short-circuited), so a concrete witness needs the concrete
        // evaluation of *all three* subterms -- `t` and `e` alike, even
        // though only one is the branch `eval_concrete` actually takes --
        // to discharge `app3(ite_ref, dc, dt, de) = lit_ref(result)`.
        Shape::If(c, t, e) => {
            let (xc, dc, pc) = eval_and_prove(store, c, combinators, params, concrete, param_facts)?;
            let (xt, dt, pt) = eval_and_prove(store, t, combinators, params, concrete, param_facts)?;
            let (xe, de, pe) = eval_and_prove(store, e, combinators, params, concrete, param_facts)?;
            let fact = combinators.cp.arith.assume_ite_fact(xc, xt, xe);
            let result = if xc != 0 { xt } else { xe };

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
            debug_assert_has_type(&combinators.cp.arith.p, &proof, &kernel::id(int_ty, lhs.clone(), rhs), "eval_and_prove: If proof");
            Some((result, lhs, proof))
        }
        Shape::SelfCall(_) | Shape::OtherCall | Shape::Combinator { .. } => None,
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
    params: &[Expr],
    concrete: &[i64],
    param_facts: &[Expr],
) -> Option<(i64, Expr, Expr)> {
    if callee_param_types.iter().any(Option::is_some) {
        return None;
    }

    // Evaluate each argument in the *outer* frame, application order.
    let mut arg_triples = Vec::with_capacity(args.len());
    for &a in args {
        let (x, d, p) = eval_and_prove(store, a, combinators, params, concrete, param_facts)?;
        arg_triples.push((x, d, p));
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
        let d = params.get(rel)?.clone();
        let p = param_facts.get(rel)?.clone();
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
    cap_triples: &[(i64, Expr, Expr)],
    arg_triples: &[(i64, Expr, Expr)],
) -> Option<(i64, Expr, Expr)> {
    let (root_arity, root_body, root_is_rec) = compile::peel(store, root)?;
    let root_captures = compile::free_vars(store, root_body, root_arity, root_is_rec);
    let n = root_captures.len();

    // The computation-rule axiom for `root` -- its own first use for this
    // `Hash` may lazily push (and, transitively, `call_ref`/`mk_env_ref`
    // for this exact shape too).
    let axiom = combinators.call_eq_ref(root)?;

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
        let cd: Vec<Expr> = cap_triples.iter().map(|(_, d, _)| d.clone()).collect();
        let lit_c: Vec<Expr> = cap_triples
            .iter()
            .map(|&(x, _, _)| {
                combinators.cp.arith.lit(x);
                combinators.cp.arith.lit_ref(x)
            })
            .collect();
        let cp: Vec<Expr> = cap_triples.iter().map(|(_, _, p)| p.clone()).collect();
        let env_eq = kernel::cong_n(&int_ty, &env_ty_expr, &mk_env_expr, &cd, &lit_c, cp);
        let denoted_env = apply_n(mk_env_expr.clone(), cd);
        let lit_env = apply_n(mk_env_expr, lit_c);
        Some((denoted_env, lit_env, env_eq, env_ty_expr))
    } else {
        None
    };

    let call_fn = combinators.call_ref(root, &root_captures, &[])?;
    let d_args: Vec<Expr> = arg_triples.iter().map(|(_, d, _)| d.clone()).collect();
    let lit_args: Vec<Expr> = arg_triples
        .iter()
        .map(|&(x, _, _)| {
            combinators.cp.arith.lit(x);
            combinators.cp.arith.lit_ref(x)
        })
        .collect();
    let p_args: Vec<Expr> = arg_triples.iter().map(|(_, _, p)| p.clone()).collect();

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
    let axiom_at_literals = apply_n(axiom.clone(), axiom_args);

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
        inner_params.push(l.clone());
        inner_concrete.push(x);
        inner_facts.push(kernel::refl(l));
    }
    if let Some(&max_rel) = root_captures.iter().max() {
        let pad_len = root_arity + max_rel as usize + 1;
        let (fx0, _, _) = cap_triples[0];
        combinators.cp.arith.lit(fx0);
        let filler = combinators.cp.arith.lit_ref(fx0);
        while inner_params.len() < pad_len {
            inner_concrete.push(fx0);
            inner_params.push(filler.clone());
            inner_facts.push(kernel::refl(filler.clone()));
        }
        for (j, &rel) in root_captures.iter().enumerate() {
            let (cx, _, _) = cap_triples[j];
            combinators.cp.arith.lit(cx);
            let l = combinators.cp.arith.lit_ref(cx);
            let idx = root_arity + rel as usize;
            inner_concrete[idx] = cx;
            inner_params[idx] = l.clone();
            inner_facts[idx] = kernel::refl(l);
        }
    }
    // `eval_and_prove`'s own recursion below (over `root_body`) may push
    // further postulates (`assume_prim_fact`/`assume_ite_fact`, fresh
    // literals); a pushed `Const` shifts nothing already built above
    // (`RELATED_WORK.md` §69), so nothing here needs re-resolving after it.
    let (result, denote_lit, proof_d) = eval_and_prove(store, root_body, combinators, &inner_params, &inner_concrete, &inner_facts)?;

    // Chain: call_at_denoted = call_at_lit_env_lit_args (bridge)
    //      = denote(root_body, [lit_args, lit_caps]) (axiom_at_literals)
    //      = lit_ref(result) (proof_d)
    let int_ty2 = combinators.cp.arith.int_ty();
    let result_ref = combinators.cp.arith.lit_ref(result);
    let bridge_to_denote =
        kernel::trans_proof(&int_ty2, &call_at_denoted, &call_at_lit_env_lit_args, &denote_lit, bridge, axiom_at_literals);
    let final_proof = kernel::trans_proof(&int_ty2, &call_at_denoted, &denote_lit, &result_ref, bridge_to_denote, proof_d);
    debug_assert_has_type(
        &combinators.cp.arith.p,
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
/// captures resolved to `(i64, Expr, Expr)` triples, ready for
/// `eval_and_prove_direct_call` once a value is actually *called* (not
/// merely *created*) -- whichever branch the `If` concretely selects.
/// `None` if `inner` is itself self-recursive (not expected to arise here
/// -- `clo_eq_ref`'s own classification already requires a bare
/// `Term::Abs`, never `Term::Rec` -- but checked rather than assumed).
/// A concrete `(value, denoted, proof)` triple per resolved argument or
/// capture -- shared alias for the `Vec` of these `eval_and_prove_call`'s
/// own family of functions passes around, just to keep the type simple
/// enough for `clippy::type_complexity` not to flag it.
type ValueTriples = Vec<(i64, Expr, Expr)>;

/// `build_clo_call_bridge`'s own return: `(call_at_denoted,
/// call_at_lit_env_lit_args, bridge, axiom_at_literals, inner_params,
/// inner_concrete, inner_facts, k, shape)` -- see its own docs. A type
/// alias purely to keep this under `clippy::type_complexity`'s own
/// threshold, same rationale as `ValueTriples`.
type CloCallBridge = (Expr, Expr, Expr, Expr, Vec<Expr>, Vec<i64>, Vec<Expr>, usize, ClosureRhsShape);

fn inner_closure_literal_value(
    combinators: &mut ClosureCombinators<'_>,
    inner: Hash,
    inner_params: &[Expr],
    inner_concrete: &[i64],
    inner_facts: &[Expr],
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
        let d = inner_params.get(rel)?.clone();
        let p = inner_facts.get(rel)?.clone();
        cap_triples.push((x, d, p));
    }
    let inner_dummy: Vec<Option<usize>> = vec![None; inner_captures.iter().map(|&r| r as usize + 1).max().unwrap_or(0)];
    let sym = combinators.register(inner, &inner_captures, &inner_dummy)?;
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
        let mk_env_expr = combinators.cp.mk_env_ref(&inner_sig);
        kernel::app(sym, apply_n(mk_env_expr, lit_c))
    };
    Some((value, cap_triples))
}

/// `eval_and_prove`'s own `AppShape::LitLambdaOver` case: a self-call
/// argument (or leaf expression) that over-applies a literal lambda
/// `root` -- `root`'s own saturated call (its first `root_arity`
/// arguments) returns a `Clo_k`, and the *extra* `k` arguments are then
/// dispatched against that closure directly. See `clo_eq_ref`'s
/// own docs for why this needs a second computation-rule axiom (root's
/// saturated call is just as opaque, `Clo`-typed, as a `call_eq_ref`-
/// covered `Int`-typed one), `ite_clo_eq_ref`'s own docs for the branch-
/// selection bridge an `If`-shaped body needs, and `apply_clo_eq_ref`'s
/// own docs for tying whichever closure value is concretely produced to
/// `call_ref(root)`'s own value.
///
/// Guarded by `combinator_return_type(root) == Some(Some(k))` and
/// `args.len() == root_arity + k` (the whole thing fully resolves to
/// `Int` -- matches `denote_with_placeholders`'s own identical
/// requirement, enforced there by calling the `Clo_k` value directly with
/// exactly `k` `Int` arguments) -- `None` otherwise, not an error: a
/// partial or chained over-application, or one whose own saturated call stays `Int`
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
    sat_arg_triples: &[(i64, Expr, Expr)],
    outer_params: &[Expr],
    outer_concrete: &[i64],
    outer_facts: &[Expr],
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
        let d = outer_params.get(rel)?.clone();
        let p = outer_facts.get(rel)?.clone();
        cap_triples.push((x, d, p));
    }
    let n = subject_captures.len();

    // The `Clo_k`-typed computation-rule axiom for `subject`'s own
    // saturated call -- its own first use for this `Hash` may lazily push
    // (and transitively `call_ref`/`mk_env_ref`/`register`/`ite_clo_ref`
    // for this exact shape too, see its own docs).
    let (axiom, shape) = combinators.clo_eq_ref(subject)?;

    let sig: Vec<Option<usize>> = vec![None; n];

    // Congruence bridge over `call_ref(subject)`'s own arguments --
    // identical construction to `eval_and_prove_direct_call`'s own (see
    // its docs), generalized to the `Clo_k` codomain here instead of
    // `Int`. `int_ty` is an already-pushed postulate's `Const`; `clo_ty`
    // is pure and never pushes -- a later push elsewhere can't invalidate
    // either (`RELATED_WORK.md` §69).
    let env_bridge = if n > 0 {
        let mk_env_expr = combinators.cp.mk_env_ref(&sig);
        let env_ty_expr = combinators.cp.env_ty(&sig);
        let cd: Vec<Expr> = cap_triples.iter().map(|(_, d, _)| d.clone()).collect();
        let lit_c: Vec<Expr> = cap_triples
            .iter()
            .map(|&(x, _, _)| {
                combinators.cp.arith.lit(x);
                combinators.cp.arith.lit_ref(x)
            })
            .collect();
        let cp: Vec<Expr> = cap_triples.iter().map(|(_, _, p)| p.clone()).collect();
        let int_ty = combinators.cp.arith.int_ty();
        let env_eq = kernel::cong_n(&int_ty, &env_ty_expr, &mk_env_expr, &cd, &lit_c, cp);
        let denoted_env = apply_n(mk_env_expr.clone(), cd);
        let lit_env = apply_n(mk_env_expr, lit_c);
        Some((denoted_env, lit_env, env_eq, env_ty_expr))
    } else {
        None
    };

    let call_fn = combinators.call_ref(subject, &subject_captures, &[])?;
    let d_sat_args: Vec<Expr> = sat_arg_triples.iter().map(|(_, d, _)| d.clone()).collect();
    let lit_sat_args: Vec<Expr> = sat_arg_triples
        .iter()
        .map(|&(x, _, _)| {
            combinators.cp.arith.lit(x);
            combinators.cp.arith.lit_ref(x)
        })
        .collect();
    let p_sat_args: Vec<Expr> = sat_arg_triples.iter().map(|(_, _, p)| p.clone()).collect();

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
    let axiom_at_literals = apply_n(axiom.clone(), axiom_args);

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
        inner_params.push(l.clone());
        inner_concrete.push(x);
        inner_facts.push(kernel::refl(l));
    }
    if let Some(&max_rel) = subject_captures.iter().max() {
        let pad_len = subject_arity + max_rel as usize + 1;
        let (fx0, _, _) = cap_triples[0];
        combinators.cp.arith.lit(fx0);
        let filler = combinators.cp.arith.lit_ref(fx0);
        while inner_params.len() < pad_len {
            inner_concrete.push(fx0);
            inner_params.push(filler.clone());
            inner_facts.push(kernel::refl(filler.clone()));
        }
        for (j, &rel) in subject_captures.iter().enumerate() {
            let (cx, _, _) = cap_triples[j];
            combinators.cp.arith.lit(cx);
            let l = combinators.cp.arith.lit_ref(cx);
            let idx = subject_arity + rel as usize;
            inner_concrete[idx] = cx;
            inner_params[idx] = l.clone();
            inner_facts[idx] = kernel::refl(l);
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
/// through (there is only ever one final `apply_*_eq_ref` step in the
/// whole chain, applied once `chosen` is finally reached), so every
/// recursive call threads the same ones through unchanged.
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
/// bridging `chosen_value`, called directly, down to a direct call on
/// `chosen`.
#[allow(clippy::too_many_arguments)]
fn resolve_closure_shape_to_leaf(
    store: &TermStore,
    combinators: &mut ClosureCombinators<'_>,
    call_at_denoted: &Expr,
    call_at_lit_env_lit_args: &Expr,
    bridge: &Expr,
    axiom_at_literals: &Expr,
    shape: &ClosureRhsShape,
    inner_params: &[Expr],
    inner_concrete: &[i64],
    inner_facts: &[Expr],
    k: usize,
    extra_arg_triples: &[(i64, Expr, Expr)],
) -> Option<(Hash, ValueTriples, ValueTriples, Expr, Expr, Expr)> {

    match shape {
        ClosureRhsShape::IfTree(tree) => {
            let leaf_shapes = classify_closure_if_tree_leaves(store, tree, k)?;
            let (resolution, tree_value_at_literals, leaf_value, tree_to_leaf_value) =
                resolve_closure_if_tree(store, combinators, tree, &leaf_shapes, inner_params, inner_concrete, inner_facts, k, extra_arg_triples)?;

            let call_at_denoted_here = call_at_denoted.clone();
            let call_at_lit_env_lit_args_here = call_at_lit_env_lit_args.clone();
            let bridge_here = bridge.clone();
            let axiom_at_literals_here = axiom_at_literals.clone();
            let clo_ty = combinators.cp.clo_ty(k);

            // `axiom_at_literals`'s own RHS is exactly the tree's own
            // formula at literals (`tree_value_at_literals`, independently
            // reconstructed here the same way `resolve_closure_if_tree`'s
            // own recursive descent builds it) -- bridge `subject`'s call
            // to that formula, then to the concretely-reached leaf's own
            // *canonical* value, via `tree_to_leaf_value` (one
            // `ite_clo_eq_ref` step per internal node on the path actually
            // taken). For a `Direct` (`Abs`/`Pap`) leaf, that canonical
            // value already *is* the final `chosen_value`; for an
            // `Indirect` (`Call`-shaped) leaf, one further bridge
            // (`leaf_to_chosen`, already built by `resolve_closure_if_tree`'s
            // own recursion) is composed below.
            let root_to_tree_value =
                kernel::trans_proof(&clo_ty, &call_at_denoted_here, &call_at_lit_env_lit_args_here, &tree_value_at_literals, bridge_here, axiom_at_literals_here);
            let root_to_leaf_value = kernel::trans_proof(&clo_ty, &call_at_denoted_here, &tree_value_at_literals, &leaf_value, root_to_tree_value, tree_to_leaf_value);

            match resolution {
                IfTreeLeafResolution::Direct { chosen, cap_triples: chosen_cap_triples, arg_prefix: chosen_arg_prefix } => {
                    // `apply_clo_eq_ref(chosen)` (a bare `Abs`-shaped leaf,
                    // exactly `k`-ary already) or `apply_pap_eq_ref(chosen, s)`
                    // (a `Pap`-shaped leaf, `chosen` there being `g`, whose
                    // own arity is `s + k`) -- `chosen_arg_prefix` is empty
                    // for the former and non-empty for the latter (a
                    // `Pap`-shaped leaf's own classification requires at
                    // least one supplied arg, see
                    // `classify_closure_if_tree_leaf`), so it doubles as the
                    // dispatch signal here without threading a separate
                    // flag.
                    let s = chosen_arg_prefix.len();
                    let apply_axiom = if s == 0 { combinators.apply_clo_eq_ref(chosen)? } else { combinators.apply_pap_eq_ref(chosen, s)? };

                    let root_to_chosen = root_to_leaf_value.clone();
                    let chosen_value_lit = leaf_value.clone();

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
                        .chain(chosen_arg_prefix.iter().map(|(_, d, _)| d.clone()))
                        .chain(extra_arg_triples.iter().rev().map(|(_, d, _)| d.clone()))
                        .collect();
                    let apply_eq_chosen = apply_n(apply_axiom.clone(), apply_axiom_args);

                    let mut chosen_arg_triples = chosen_arg_prefix;
                    chosen_arg_triples.extend(extra_arg_triples.iter().cloned());

                    Some((chosen, chosen_cap_triples, chosen_arg_triples, chosen_value_lit, root_to_chosen, apply_eq_chosen))
                }
                IfTreeLeafResolution::Indirect { chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, leaf_to_chosen, apply_eq_chosen } => {
                    // The reached leaf was itself `Call`-shaped:
                    // `leaf_value` (this level's own canonical value for
                    // it) already has its own further resolution down to a
                    // genuine literal-lambda `chosen`, fully composed by
                    // `resolve_closure_if_tree`'s own recursive
                    // `resolve_closure_shape_to_leaf` call -- compose
                    // `root_to_leaf_value` with `leaf_to_chosen` to reach
                    // `chosen_value`, and reuse `apply_eq_chosen` as-is (it
                    // already covers the full "call with all args" fact --
                    // building a second one here would double-count).
                    let root_to_chosen = kernel::trans_proof(&clo_ty, &call_at_denoted_here, &leaf_value, &chosen_value, root_to_leaf_value, leaf_to_chosen);
                    Some((chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, root_to_chosen, apply_eq_chosen))
                }
            }
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
                let d = inner_params.get(rel)?.clone();
                let p = inner_facts.get(rel)?.clone();
                g_cap_triples.push((x, d, p));
            }

            let mut supplied_triples = Vec::with_capacity(s);
            for &a in args {
                let (x, d, p) = eval_and_prove(store, a, combinators, inner_params, inner_concrete, inner_facts)?;
                supplied_triples.push((x, d, p));
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

            let call_at_denoted_here = call_at_denoted.clone();
            let call_at_lit_env_lit_args_here = call_at_lit_env_lit_args.clone();
            let bridge_here = bridge.clone();
            let axiom_at_literals_here = axiom_at_literals.clone();
            let clo_ty = combinators.cp.clo_ty(k);

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
            let pap_at_denoted = apply_n(pap_fn, pap_args);

            let root_to_chosen =
                kernel::trans_proof(&clo_ty, &call_at_denoted_here, &call_at_lit_env_lit_args_here, &pap_at_denoted, bridge_here, axiom_at_literals_here);

            // `apply_pap_eq_ref(g, s)` -- its own first use for this
            // `(g, s)` may lazily push.
            let apply_axiom = combinators.apply_pap_eq_ref(g, s)?;

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
                .chain(supplied_triples.iter().map(|(_, d, _)| d.clone()))
                .chain(extra_arg_triples.iter().rev().map(|(_, d, _)| d.clone()))
                .collect();
            let apply_eq_chosen = apply_n(apply_axiom.clone(), apply_axiom_args);

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
                g_arg_triples.push((x, d, p));
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
            let call_at_denoted_here = call_at_denoted.clone();
            let call_at_lit_env_lit_args_here = call_at_lit_env_lit_args.clone();
            let bridge_here = bridge.clone();
            let axiom_at_literals_here = axiom_at_literals.clone();
            let clo_ty = combinators.cp.clo_ty(k);
            let root_to_g = kernel::trans_proof(&clo_ty, &call_at_denoted_here, &call_at_lit_env_lit_args_here, &g_call_at_denoted, bridge_here, axiom_at_literals_here);

            let (chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, g_to_chosen, apply_eq_chosen) = resolve_closure_shape_to_leaf(
                store,
                combinators,
                &g_call_at_denoted.clone(),
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
            let root_to_chosen = kernel::trans_proof(&clo_ty, call_at_denoted, &g_call_at_denoted, &chosen_value, root_to_g, g_to_chosen);
            debug_assert_has_type(
                &combinators.cp.arith.p,
                &root_to_chosen,
                &kernel::id(clo_ty, call_at_denoted.clone(), chosen_value.clone()),
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
    params: &[Expr],
    concrete: &[i64],
    param_facts: &[Expr],
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
        arg_triples.push((x, d, p));
    }
    let (sat_arg_triples, extra_arg_triples) = arg_triples.split_at(root_arity);

    let (call_at_denoted, call_at_lit_env_lit_args, bridge, axiom_at_literals, inner_params, inner_concrete, inner_facts, k, shape) =
        build_clo_call_bridge(store, combinators, root, sat_arg_triples, params, concrete, param_facts)?;
    debug_assert_eq!(k, k_check, "eval_and_prove_call_over: build_clo_call_bridge's own k must match combinator_return_type(root)");

    // `resolve_closure_shape_to_leaf` below may lazily push further
    // postulates (its own recursion into a `Call`'s own `g`, reaching
    // `apply_clo_eq_ref`/`apply_pap_eq_ref`, ...); `call_at_denoted` is
    // still needed afterward (below), the other three are only consumed
    // (cloned) inside that call.

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
    // `apply_*_eq_ref` fact bridging `chosen_value` called directly down
    // to a direct call on `chosen`.
    let (chosen, chosen_cap_triples, chosen_arg_triples, chosen_value, root_to_chosen, apply_eq_chosen) = resolve_closure_shape_to_leaf(
        store,
        combinators,
        &call_at_denoted,
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
    // literals first" step is needed at all.
    let d_extra_args: Vec<Expr> = extra_arg_triples.iter().map(|(_, d, _)| d.clone()).collect();

    // `cong1` over a `Clo_k`-typed value's own use as the callee, the `k`
    // extra args held fixed at their denoted values, using
    // `root_to_chosen` to turn `call_at_denoted` into `chosen_value` --
    // called directly (`c(args)`, no `apply_ref` axiom to route through,
    // see `RELATED_WORK.md` section 11).
    let mut f_clo_body = kernel::var(0);
    for d in &d_extra_args {
        f_clo_body = kernel::app(f_clo_body, kernel::shift(d, 0, 1));
    }
    let f_clo = kernel::lam(clo_ty.clone(), f_clo_body);
    let clo_step = kernel::cong1(&clo_ty, &int_ty2, &f_clo, call_at_denoted.clone(), chosen_value.clone(), root_to_chosen);
    let apply_at_denoted = apply_n(call_at_denoted, d_extra_args.iter().cloned());
    let apply_at_chosen_denoted_args = apply_n(chosen_value, d_extra_args.iter().cloned());

    // `eval_and_prove_direct_call`'s own recursion below (into `chosen`'s
    // own body) may push further postulates.
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
        &combinators.cp.arith.p,
        &final_proof,
        &kernel::id(int_ty3, apply_at_denoted.clone(), result_ref),
        "eval_and_prove_call_over: final proof",
    );
    Some((result, apply_at_denoted, final_proof))
}

/// See the section docs above for what this guards against.
const WITNESS_NODE_BUDGET: usize = 256;

/// The leaf `concrete`'s trace reaches: the one whose every condition
/// evaluates to its recorded outcome.
fn trace_leaf(store: &TermStore, leaves: &[Leaf], concrete: &[i64]) -> Option<usize> {
    leaves.iter().position(|leaf| leaf.path.iter().all(|&(cond, lit)| eval_concrete(store, cond, concrete) == Some(lit)))
}

/// Canonical params for one call: literals, trivially equal to themselves
/// -- see the section docs above for why this (not a caller-supplied
/// denoted expression) is what makes `build_ev_witness`'s `memo` sound.
fn canonical_params(combinators: &ClosureCombinators<'_>, concrete: &[i64]) -> (Vec<Expr>, Vec<Expr>) {
    let arith = &combinators.cp.arith;
    let params: Vec<Expr> = concrete.iter().map(|&c| arith.lit_ref(c)).collect();
    let param_facts = params.iter().map(|p| kernel::refl(p.clone())).collect();
    (params, param_facts)
}

/// Builds an actual `e : Ev(params, v)` witness for one specific call,
/// following the real trace `concrete` determines (mirroring
/// `classify_step`, but for any leaf `flatten_tree` found, not just a tail
/// loop) and recursing into every self-call occurrence found along the way.
/// Returns `(v, e)`; a caller may hold either across further postulate
/// pushes (as every caller here does) with no extra care, since a pushed
/// postulate is a `Const` and shifts nothing (`RELATED_WORK.md` §69).
/// `params`/`param_facts` are
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
    combines: &[Expr],
    ev_pos: usize,
    concrete: &[i64],
    budget: &mut usize,
    memo: &mut HashMap<Vec<i64>, (Expr, Expr)>,
) -> Option<(Expr, Expr)> {
    if let Some((v, e)) = memo.get(concrete) {
        return Some((v.clone(), e.clone()));
    }
    *budget = budget.checked_sub(1)?;

    let leaf_idx = trace_leaf(store, leaves, concrete)?;
    let leaf = &leaves[leaf_idx];
    let (params, param_facts) = canonical_params(combinators, concrete);

    let mut premises = Vec::with_capacity(leaf.path.len());
    for &(cond, _lit) in &leaf.path {
        let (_, _, proof) = eval_and_prove(store, cond, combinators, &params, concrete, &param_facts)?;
        premises.push(proof);
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
            denoted_args.push(denoted);
            denoted_facts.push(pf);
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

        // Recast `e_canonical : Ev(lit_params, v)` to `Ev(denoted_params,
        // v)` -- what *this* leaf's own `Ev` constructor actually expects
        // for its e_i (its type was built from the call's real argument
        // expressions, not just their values) -- via congruence over the
        // params (`cong_n`, `Ev` held fixed at `v`) and transport along the
        // resulting type equality.
        let int_ty = combinators.cp.arith.int_ty();
        let lit_params: Vec<Expr> = new_concrete.iter().map(|&x| combinators.cp.arith.lit_ref(x)).collect();
        let ps: Vec<Expr> = denoted_facts
            .iter()
            .zip(&denoted_args)
            .zip(&lit_params)
            .map(|((pf, dp), lp)| kernel::sym(&int_ty, dp, lp, pf.clone()))
            .collect();
        let v_resolved = v.clone();
        let f = params_and_close(&mut combinators.cp.arith, self_call.arity, kernel::Binder::Lam, |arith, pp| {
            Some(ev_of(arith, ev_pos, pp, v_resolved.clone()))
        })?;
        let ev_eq = kernel::cong_n(&int_ty, &kernel::sort(0), &f, &lit_params, &denoted_args, ps);
        let e = kernel::transport(
            0,
            ev_of(&combinators.cp.arith, ev_pos, &lit_params, v_resolved.clone()),
            ev_of(&combinators.cp.arith, ev_pos, &denoted_args, v_resolved),
            ev_eq,
            e_canonical.clone(),
        );
        vs.push(v);
        es.push(e);
    }

    let args = params.iter().cloned().chain(premises).chain(vs.iter().cloned()).chain(es);
    let e = apply_n(combinators.cp.arith.p.get(ev_leaf_positions[leaf_idx]), args);
    let v = combine_of(&combines[leaf_idx], &params, &vs);
    let int_ty_check = combinators.cp.arith.int_ty();
    debug_assert_has_type(&combinators.cp.arith.p, &v, &int_ty_check, "build_ev_witness: v");
    let ev_check = ev_of(&combinators.cp.arith, ev_pos, &params, v.clone());
    debug_assert_has_type(&combinators.cp.arith.p, &e, &ev_check, "build_ev_witness: e");
    memo.insert(concrete.to_vec(), (v.clone(), e.clone()));
    Some((v, e))
}

/// A kernel-checked witness, concrete to one call `h(args)`, that the
/// universal theorem's `loop_val` reconstruction and the value the
/// recursion actually produces agree -- see `prove_tail_recursive_instance`.
pub struct UniversalInstanceProof {
    pub globals: Globals,
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
        globals: scaffold.combinators.cp.arith.p.globals.clone(),
        arity: scaffold.arity,
        theorem_ty: scaffold.theorem_ty.clone(),
        theorem_proof: scaffold.theorem_proof.clone(),
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

    let params: Vec<Expr> = concrete.iter().map(|&c| scaffold.combinators.lit_ref(c)).collect();
    let applied = apply_n(scaffold.theorem_proof.clone(), params.into_iter().chain([v, e]));
    let ty = scaffold.combinators.cp.arith.p.infer(&applied).ok()?;
    let (lhs, rhs) = match kernel::whnf(&ty) {
        Expr::Id(_, ref lhs, ref rhs) => ((**lhs).clone(), (**rhs).clone()),
        _ => return None,
    };

    Some(UniversalInstanceProof {
        int_ty: scaffold.combinators.int_ty(),
        globals: scaffold.combinators.cp.arith.p.globals,
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
/// a caller's own `combinators` is always safe.
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

/// Refines an application-shaped [`Shape`] (from `compile::classify`, the
/// same classification `build_node` dispatches on) with what the
/// closures fragment needs to know: whether a variable callee is a
/// `Clo`-typed parameter called at its own arity, and a literal callee's
/// own parameter types. `None` for any other shape.
fn app_shape(store: &TermStore, shape: Shape, param_types: &[Option<usize>]) -> Option<AppShape> {
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
fn combinator_return_type(store: &TermStore, h: Hash) -> Option<Option<usize>> {
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
fn pap_extra_arity(store: &TermStore, root: Hash) -> usize {
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
fn return_type_of(store: &TermStore, h: Hash, arity: usize, self_idx: Option<u32>, param_types: &[Option<usize>]) -> Option<Option<usize>> {
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
fn arg_denotation(d: Denoted, want: Option<usize>, actual: impl FnOnce() -> Option<Option<usize>>) -> Option<Expr> {
    match want {
        Some(k) if actual() == Some(Some(k)) => d.clo(),
        Some(_) => None,
        None => d.int(),
    }
}

/// Extends `ArithPostulates` with postulated closure-value support -- see
/// the section docs above.
#[derive(Clone)]
struct ClosurePostulates {
    arith: ArithPostulates,
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
    fn new() -> Self {
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
    fn clo_ty(&mut self, arity: usize) -> Expr {
        self.curried_int_ty(arity)
    }

    /// The literal `Int -> .. -> Int` (`arity` copies) type -- `clo_ty`'s
    /// own core, factored out so `ite_clo_ref` can use this same shape for
    /// its own domain/codomain without calling back into `clo_ty` itself.
    fn curried_int_ty(&self, arity: usize) -> Expr {
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
    /// happen to match this exact signature, the same way `Clo_k` itself
    /// (`ClosurePostulates::clo_ty`) is shared across every closure of
    /// arity `k` regardless of which combinator it turns out to be -- two
    /// combinators that both
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
    fn mk_clo_ref(&mut self, h: Hash, sig: &[Option<usize>], arity: usize) -> Expr {
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
    fn call_ref(&mut self, h: Hash, captures: &[u32], caller_param_types: &[Option<usize>]) -> Option<Expr> {
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
    /// one, `mk_env_ref` for any leaf that captures, `ite_clo_ref(k)` for
    /// the `If` shape) may be pushed lazily from inside the
    /// `params_and_close_typed` closure below that binds `root`'s own
    /// quantified captures/params.
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
    fn clo_eq_ref_call(&mut self, root: Hash, arity: usize, body: Hash, is_rec: bool, k: usize) -> Option<(Expr, ClosureRhsShape)> {
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
    fn clo_eq_ref_pap(&mut self, root: Hash, arity: usize, body: Hash, is_rec: bool, _param_types: &[Option<usize>], k: usize) -> Option<(Expr, ClosureRhsShape)> {
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
    fn ite_clo_eq_ref(&mut self, xc: i64, arity: usize) -> Expr {
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
    fn apply_pap_eq_ref(&mut self, g: Hash, s: usize) -> Option<Expr> {
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
/// closure creation in this position"), or a leaf reached only through a
/// further *saturated* indirect call to a further literal lambda `g`
/// whose own saturated call is itself `Clo_k`-typed (mirroring
/// `ClosureRhsShape::Call`, keyed per leaf instead of per `root`).
enum ClosureIfTreeLeafShape {
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
fn classify_closure_if_tree_leaf(store: &TermStore, h: Hash, k: usize) -> Option<ClosureIfTreeLeafShape> {
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

/// An `Abs`-shaped leaf's own `register`/`mk_env_ref` value expression,
/// over abstract `params_full` -- `clo_eq_ref_if_tree`'s own single-pair
/// `value_expr`, generalized to read a leaf's own captures from
/// `captures` (from `leaf_shapes`) instead of a locally-closed-over pair.
fn closure_leaf_value_expr(combinators: &mut ClosureCombinators<'_>, leaf: Hash, captures: &[u32], params_full: &[Expr]) -> Option<Expr> {
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
fn closure_leaf_pap_value_expr(store: &TermStore, combinators: &mut ClosureCombinators<'_>, g: Hash, args: &[Hash], params_full: &[Expr]) -> Option<Expr> {
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
fn closure_leaf_call_value_expr(store: &TermStore, combinators: &mut ClosureCombinators<'_>, g: Hash, args: &[Hash], params_full: &[Expr]) -> Option<Expr> {
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
fn inner_closure_pap_value(
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
fn inner_closure_call_value(
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
fn closure_if_tree_value_at_literals(
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
enum IfTreeLeafResolution {
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
fn resolve_closure_if_tree(
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
fn capture_sig(captures: &[u32], caller_param_types: &[Option<usize>]) -> Option<Vec<Option<usize>>> {
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
fn build_env_expr(combinators: &mut ClosureCombinators, captures: &[u32], params: &[Expr], param_types: &[Option<usize>]) -> Option<Expr> {
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
fn collect_literals_closure(store: &TermStore, h: Hash, param_types: &[Option<usize>], out: &mut Vec<i64>) -> bool {
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
fn denote_closure(
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
struct ConcreteClo {
    root: Hash,
    frame: Vec<DynVal>,
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
enum DynVal {
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
enum DynDenoted {
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
/// own `Expr` value rather than a raw postulate position (see `DynVal`'s
/// own docs for why a substituted slot may hold one).
fn build_env_expr_dyn(store: &TermStore, combinators: &mut ClosureCombinators, captures: &[u32], frame: &[DynVal]) -> Option<Expr> {
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
struct DynBudget {
    steps: usize,
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
    fn new() -> Self {
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
fn eval_dyn_inline_call(
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
fn eval_dyn(store: &TermStore, h: Hash, combinators: &mut ClosureCombinators, self_ctx: Option<(Hash, usize)>, budget: &mut DynBudget, frame: &[DynVal]) -> Option<DynDenoted> {
    kernel::grow(|| eval_dyn_node(store, h, combinators, self_ctx, budget, frame))
}

/// [`eval_dyn`]'s body.
fn eval_dyn_node(store: &TermStore, h: Hash, combinators: &mut ClosureCombinators, self_ctx: Option<(Hash, usize)>, budget: &mut DynBudget, frame: &[DynVal]) -> Option<DynDenoted> {
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

#[cfg(test)]
mod tests;
