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
//! ## Tail recursion: a universal proof (`prove_tail_recursive_universal`)
//!
//! A *universal* proof ("for every input, the recursive reading and the
//! loop reading agree", not just at the sampled/traced points) needs real
//! induction on the call depth. Since this project's kernel is predicative
//! (see `kernel`'s docs), there's no bare inductive `Nat` to induct on --
//! instead, `prove_tail_recursive_universal` postulates a family
//! `Ev(params, v) : Sort(0)`, "the tail-call trace starting at `params`
//! evaluates to `v`", with its own two constructors (`ev_base`: the base
//! case terminates at its own value; `ev_step`: one more tail-call step
//! prepended to an already-known trace) and a postulated recursor
//! (`ev_rec`) obeying the same universal-motive shape `kernel::WRec` uses,
//! just for this specific inductive family instead of a derived `W`-type
//! (same "postulated inductive family" pattern as `kernel::Postulates`'
//! docs). Applying `ev_rec` with the constant-`Int` motive gives
//! `loop_val`, a term computing exactly what the compiled loop computes,
//! with the two computation-rule axioms `loop_val` needs (specific to
//! *this* `loop_val`, not a generic schema) postulated the same way. The
//! theorem itself -- `loop_val(params, v, e) = v` for every `params`, `v`,
//! and every trace `e : Ev(params, v)` -- is then a genuine `ev_rec`
//! induction using `kernel::cong1`/`trans_proof` as its step case's
//! composition lemmas, not a per-call trace unrolling. It covers exactly
//! the same shape `prove_tail_recursive_call` does (a single `If` whose two
//! branches are a base case and a fully-saturated tail self-call); deeper
//! branching is future work.

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

// --- tail recursion: a universal proof, via genuine induction -----------
//
// `prove_tail_recursive_call` gives a certificate per call. The universal
// version -- one theorem covering *every* call -- needs real induction on
// how many tail-call iterations occur, which varies with the input. Since
// `Int` is postulated (no internal structure to induct on) and any
// well-founded measure is specific to the function (gcd's `b` decreases;
// a different tail-recursive function would need a different measure),
// this is stated the standard way partial/possibly-nonterminating
// correctness results are: *conditionally* on a witness that the
// recursion actually terminates, rather than by also proving termination.
//
// That witness is `Ev(params, v)`: "unrolling from `params` reaches `v`",
// an inductively-defined relation with exactly the two constructors
// `compile_node`'s loop has cases for (reach a base value directly, or
// take one more tail-call step). Bootstrapping it as a genuine `W`-type
// hits the same wall as any other finite-shaped inductive in this kernel
// (see `kernel::Postulates`' docs), so -- consistent with everything else
// in this module -- it's postulated: the type family (`Ev`), its two
// constructors (`ev_base`/`ev_step`), and a generic eliminator (`ev_rec`,
// used twice below, with two different motives).
//
// `loop_val` is then *defined* via that eliminator -- not postulated --
// with exactly the recursive shape `compile_node`'s loop has: return the
// base value directly, or return whatever the recursive step already
// computed. Since a postulated eliminator has no built-in reduction rule
// the way `WRec` does, its two computation rules for *this specific*
// `loop_val` are postulated directly as propositional (`Id`-typed) axioms
// (`loop_val_base_eq`/`loop_val_step_eq`) -- not as a fully generic "for
// any motive" schema, since `loop_val` is the only thing that needs them.
//
// The theorem -- `Pi params v (e : Ev(params,v)). Id(Int, loop_val(params,v,e), v)`
// -- says the witness's own claimed value is always what `loop_val`
// reconstructs from it, and is proved by one more use of `ev_rec` (motive:
// the theorem statement itself), whose base case is `loop_val_base_eq`
// directly and whose step case chains `loop_val_step_eq` with the
// induction hypothesis via `kernel::trans_proof`.
//
// Scope: `body` must be `If(cond, branch_a, branch_b)` with exactly one
// branch a base case and the other a tail call -- i.e. gcd's shape.
// Deeper If-nesting is future work (same kind of restriction as
// elsewhere in this module: a real gap, not a subtle one).

/// `f` applied to each of `args` in order (left to right).
fn apply_n(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, kernel::app)
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
/// the interpreter's recursion terminates (`Ev`) determines the same
/// value the compiled loop's own recursive structure (`loop_val`)
/// reconstructs from that witness.
pub struct UniversalTailProof {
    pub ctx: Ctx,
    pub arity: usize,
    /// `: Pi p_0..p_{arity-1} v (e : Ev(p_0,..,v)). Id(Int, loop_val(..,e), v)`.
    pub theorem_ty: Expr,
    pub theorem_proof: Expr,
}

/// Attempts to build a [`UniversalTailProof`] for `h`. Returns `None` for
/// anything outside the covered fragment: not `Rec`-wrapped, zero arity,
/// or a body that isn't `If(cond, branch_a, branch_b)` with exactly one
/// branch a base case and the other a fully-saturated tail self-call (see
/// module docs).
pub fn prove_tail_recursive_universal(store: &TermStore, h: Hash) -> Option<UniversalTailProof> {
    let (arity, body, is_rec) = compile::peel(store, h)?;
    if !is_rec || arity == 0 {
        return None;
    }
    let self_idx = arity as u32;

    let Term::If(c, ba, bb) = store.resolve(body) else {
        return None;
    };
    let (cond, branch_a, branch_b) = (*c, *ba, *bb);
    let (base_expr, tail_args_expr) = match (
        compile::match_self_call(store, branch_a, arity, Some(self_idx)),
        compile::match_self_call(store, branch_b, arity, Some(self_idx)),
    ) {
        (None, Some(args)) => (branch_a, args),
        (Some(args), None) => (branch_b, args),
        _ => return None, // both or neither branch is a tail call -- not this shape
    };
    if tail_args_expr.len() != arity {
        return None;
    }

    let mut lits = Vec::new();
    let in_fragment = collect_literals(store, cond, arity, None, &mut lits)
        && collect_literals(store, base_expr, arity, None, &mut lits)
        && tail_args_expr
            .iter()
            .all(|&e| collect_literals(store, e, arity, None, &mut lits));
    if !in_fragment {
        return None;
    }

    let mut arith = ArithPostulates::new();
    for n in lits {
        arith.lit(n);
    }

    // new_params(params): the tail call's argument expressions denoted in
    // terms of `params`, reindexed from application order to by-`Var`
    // order (matching `prove_tail_recursive_call`'s convention exactly).
    // Always resolves `pp` fresh, so it's safe to call at any point,
    // however many more things have been pushed since `pp` was created.
    let new_params = |arith: &ArithPostulates, pp: &Params| -> Option<Vec<Expr>> {
        let params = pp.at(arith);
        (0..arity)
            .map(|i| denote(store, tail_args_expr[arity - 1 - i], arith, &params))
            .collect()
    };

    // Ev : Int^arity -> Int -> Sort(0)  (non-dependent chain: composes
    // correctly via `arrow`'s own shifting regardless of build order --
    // see `ArithPostulates::new`'s `ite_ty` for the same pattern.)
    let arrow_chain = |arith: &ArithPostulates| -> Expr {
        let mut ty = kernel::sort(0);
        for _ in 0..=arity {
            ty = kernel::arrow(arith.int_ty(), ty);
        }
        ty
    };
    let ev_ty = arrow_chain(&arith);
    let ev_pos = arith.p.push(ev_ty);
    // Resolves `params`/`np` fresh via the caller-supplied slice -- the
    // caller is responsible for passing one resolved *at the current
    // depth* (`pp.at(arith)` or a freshly-recomputed `new_params`), not a
    // cached one from before further pushes.
    let ev_of = |arith: &ArithPostulates, params: &[Expr], v: Expr| -> Expr {
        apply_n(arith.p.get(ev_pos), params.iter().cloned().chain([v]))
    };

    // ev_base : Pi params:Int^arity. Ev(params, denote(base_expr, params))
    let ev_base_ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
        let params = pp.at(arith);
        let v = denote(store, base_expr, arith, &params)?;
        Some(ev_of(arith, &params, v))
    })?;
    let ev_base_pos = arith.p.push(ev_base_ty);

    // ev_step : Pi params:Int^arity. Pi v:Int. Ev(new_params, v) -> Ev(params, v)
    let ev_step_ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
        let v_pos = arith.p.push(arith.int_ty());
        // `new_params` called *after* pushing v (it doesn't need v, but
        // must reflect this depth to stay valid once used here).
        let np = new_params(arith, pp)?;
        let premise = ev_of(arith, &np, arith.p.get(v_pos));
        let concl = ev_of(arith, &pp.at(arith), arith.p.get(v_pos));
        Some(kernel::arrow(premise, concl))
    })?;
    let ev_step_pos = arith.p.push(ev_step_ty);

    // Generic recursor:
    // ev_rec : Pi P:(Pi params:Int^arity. Pi v:Int. Ev(params,v) -> Sort(0)).
    //          (Pi params. P(params, denote(base_expr,params), ev_base(params)))
    //       -> (Pi params v (e:Ev(new_params,v)). P(new_params,v,e) -> P(params,v,ev_step(params,v,e)))
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

    let base_case_ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
        let params = pp.at(arith);
        let v = denote(store, base_expr, arith, &params)?;
        let eb = apply_n(arith.p.get(ev_base_pos), params.iter().cloned());
        Some(p_of(arith, &params, v, eb))
    })?;
    let step_case_ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
        // Push phase: each push's own type may only use what's already
        // resolved *so far* (fine -- that's ordinary dependent formation).
        // `new_params` is called *after* pushing v, immediately before the
        // one use that needs it, so it reflects this depth correctly.
        let v_pos = arith.p.push(arith.int_ty());
        let np = new_params(arith, pp)?;
        let ev_np = ev_of(arith, &np, arith.p.get(v_pos));
        let e_pos = arith.p.push(ev_np);
        // Use phase: every push for this closure is done, so resolve
        // *everything* fresh here rather than reusing anything captured
        // during the push phase (which would be stale by however many
        // pushes happened after it).
        let np2 = new_params(arith, pp)?;
        let params = pp.at(arith);
        let v = arith.p.get(v_pos);
        let e = arith.p.get(e_pos);
        let ih = p_of(arith, &np2, v.clone(), e.clone());
        let es = apply_n(arith.p.get(ev_step_pos), params.iter().cloned().chain([v.clone(), e]));
        let concl = p_of(arith, &params, v, es);
        Some(kernel::arrow(ih, concl))
    })?;
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

    let ev_rec_ty_body = kernel::arrow(base_case_ty, kernel::arrow(step_case_ty, concl_ty));
    let ev_rec_ty = kernel::close_pi(p_base_len, &arith.p.ctx, ev_rec_ty_body);
    arith.p.ctx.truncate(p_base_len);
    let ev_rec_pos = arith.p.push(ev_rec_ty);
    let ev_rec_ref = |arith: &ArithPostulates,
                       motive: Expr,
                       base: Expr,
                       step: Expr,
                       params: &[Expr],
                       v: Expr,
                       e: Expr|
     -> Expr {
        apply_n(
            arith.p.get(ev_rec_pos),
            [motive, base, step].into_iter().chain(params.iter().cloned()).chain([v, e]),
        )
    };

    // loop_val's two arguments to ev_rec, using the constant motive `Int`:
    //   base' : Pi params. Int  =  \params. denote(base_expr, params)
    //   step' : Pi params v e. Int -> Int  =  \params v e ih. ih
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
    let loop_base_expr = params_and_close(&mut arith, arity, kernel::close_lam, |arith, pp| {
        denote(store, base_expr, arith, &pp.at(arith))
    })?;
    let loop_base = Anchored::new(&arith, loop_base_expr);
    let loop_step_expr = params_and_close(&mut arith, arity, kernel::close_lam, |arith, pp| {
        let v_pos = arith.p.push(arith.int_ty());
        // Matches `step_case_ty`'s own signature: the step function's `e`
        // binder is `Ev(new_params, v)`, not `Ev(params, v)` -- it's the
        // premise about the *recursive call's* trace, not this call's.
        let np = new_params(arith, pp)?;
        let ev_np = ev_of(arith, &np, arith.p.get(v_pos));
        arith.p.push(ev_np); // e : Ev(new_params, v)
        let ih_pos = arith.p.push(arith.int_ty()); // ih : Int (const_int_motive always gives Int)
        Some(arith.p.get(ih_pos))
    })?;
    let loop_step = Anchored::new(&arith, loop_step_expr);

    let loop_val = |arith: &ArithPostulates, params: &[Expr], v: Expr, e: Expr| -> Expr {
        ev_rec_ref(
            arith,
            const_int_motive.at(arith),
            loop_base.at(arith),
            loop_step.at(arith),
            params,
            v,
            e,
        )
    };

    // Two specific computation-rule axioms for *this* `loop_val` (not a
    // generic "for any motive" schema -- see module docs).
    let loop_val_base_eq_ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
        let params = pp.at(arith);
        let v = denote(store, base_expr, arith, &params)?;
        let eb = apply_n(arith.p.get(ev_base_pos), params.iter().cloned());
        let lhs = loop_val(arith, &params, v.clone(), eb);
        Some(kernel::id(arith.int_ty(), lhs, v))
    })?;
    let loop_val_base_eq_pos = arith.p.push(loop_val_base_eq_ty);

    let loop_val_step_eq_ty = params_and_close(&mut arith, arity, kernel::close_pi, |arith, pp| {
        let v_pos = arith.p.push(arith.int_ty());
        let np = new_params(arith, pp)?;
        let ev_np = ev_of(arith, &np, arith.p.get(v_pos));
        let e_pos = arith.p.push(ev_np);
        // Use phase.
        let np2 = new_params(arith, pp)?;
        let params = pp.at(arith);
        let v = arith.p.get(v_pos);
        let e = arith.p.get(e_pos);
        let es = apply_n(arith.p.get(ev_step_pos), params.iter().cloned().chain([v.clone(), e.clone()]));
        let lhs = loop_val(arith, &params, v.clone(), es);
        let rhs = loop_val(arith, &np2, v, e);
        Some(kernel::id(arith.int_ty(), lhs, rhs))
    })?;
    let loop_val_step_eq_pos = arith.p.push(loop_val_step_eq_ty);

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

    let theorem_base_expr = params_and_close(&mut arith, arity, kernel::close_lam, |arith, pp| {
        Some(apply_n(arith.p.get(loop_val_base_eq_pos), pp.at(arith)))
    })?;
    let theorem_base = Anchored::new(&arith, theorem_base_expr);

    let theorem_step_expr = params_and_close(&mut arith, arity, kernel::close_lam, |arith, pp| {
        let v_pos = arith.p.push(arith.int_ty());
        let np = new_params(arith, pp)?;
        let ev_np = ev_of(arith, &np, arith.p.get(v_pos));
        let e_pos = arith.p.push(ev_np);

        // ih's type needs v/e fresh (after e's own push).
        let np2 = new_params(arith, pp)?;
        let ih_ty = kernel::id(
            arith.int_ty(),
            loop_val(arith, &np2, arith.p.get(v_pos), arith.p.get(e_pos)),
            arith.p.get(v_pos),
        );
        let ih_pos = arith.p.push(ih_ty);

        // Use phase: every push for this closure is done.
        let np3 = new_params(arith, pp)?;
        let params = pp.at(arith);
        let v = arith.p.get(v_pos);
        let e = arith.p.get(e_pos);
        let ih = arith.p.get(ih_pos);

        // step_eq : Id(Int, loop_val(params,v,ev_step(params,v,e)), loop_val(new_params,v,e))
        let es = apply_n(arith.p.get(ev_step_pos), params.iter().cloned().chain([v.clone(), e.clone()]));
        let step_eq =
            apply_n(arith.p.get(loop_val_step_eq_pos), params.iter().cloned().chain([v.clone(), e.clone()]));

        let lhs = loop_val(arith, &params, v.clone(), es);
        let mid = loop_val(arith, &np3, v.clone(), e);
        Some(kernel::trans_proof(&arith.int_ty(), &lhs, &mid, &v, step_eq, ih))
    })?;
    let theorem_step = Anchored::new(&arith, theorem_step_expr);

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
        Some(ev_rec_ref(
            arith,
            id_motive.at(arith),
            theorem_base.at(arith),
            theorem_step.at(arith),
            &params,
            v,
            e,
        ))
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
    fn non_tail_recursion_is_out_of_scope_for_the_universal_proof() {
        // Same factorial as the non-tail-recursion test below, but for the
        // universal proof this time.
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

        assert!(prove_tail_recursive_universal(&s, fact).is_none());
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
