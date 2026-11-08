//! Analyses a term in a restricted "first-order arithmetic with
//! self-recursion and closures" fragment of the term language and builds
//! the JIT's IR (`ir.rs`), which `lower_wat.rs` turns into WebAssembly text
//! (WAT) — our formalization of the target machine. `wasmtime` then
//! JIT-compiles that WAT (via Cranelift) to native code.
//!
//! Only a subset of terms fall in this fragment: closed expressions built
//! from `Var`/`Lit`/`Prim`/`If`, fully-saturated self-calls (optionally
//! wrapped in `Rec` for recursion), fully-saturated applications of
//! either a variable (a parameter *or* a captured free variable) or a
//! literal lambda value ("combinator" below, *capturing* or not) holding a
//! closure, an *under*-applied literal lambda (real partial application),
//! and an *over*-applied literal lambda (calling whatever its saturated
//! call returns with more arguments). A variable applied with inconsistent
//! arities across call sites is also in the fragment, via a curried
//! single-argument dispatch fallback (`ArityUse::Inconsistent`, which makes
//! the module `ir::Dispatch::Curried`). Anything else (a genuinely
//! free/unbound variable, ...) is rejected by returning `None`, and the
//! caller falls back to the interpreter — the JIT never has to be
//! complete, only sound about what it accepts.
//!
//! This module holds the combinator registry and the builder (`build`); term
//! shape (`classify`, `free_vars`, closure-arity inference, shared with
//! `proof.rs`) is in `shape.rs`. How the IR becomes Wasm --
//! the closure representation, partial application, over-application and
//! generic dispatch -- is documented where it is implemented, in
//! `lower_wat.rs`'s module docs.

use std::sync::atomic::{AtomicUsize, Ordering};

use hashbrown::HashMap;

use crate::jit::ir;
use crate::jit::shape::{ArityUse, Shape, classify, free_vars, infer_closure_arities, is_comparison, local_index, peel};
use crate::lang::term::{Hash, Term, TermStore};
use tatic_wasm::print::print_body;
use tatic_wasm::wasm::Ins;

/// One piece of a compiled module, in print order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    /// Module scaffolding printed verbatim: templates, `(type ..)`,
    /// `(table ..)`/`(elem ..)` lines, the export.
    Text(String),
    /// A lowered function: its signature and local declarations, then its
    /// body (a wrapping `Loop`), then the closing paren.
    Func { name: String, header: String, body: Vec<Ins> },
}

pub struct CompiledFragment {
    pub arity: usize,
    pub module: Vec<Item>,
    /// Whether the module exports a mutable `"hp"` global (the bump
    /// allocator's next-free-byte pointer) that `jit.rs` must reset to 0
    /// before *every* top-level call. `jit.rs` caches and reuses one
    /// compiled instance across many calls, so without a reset every
    /// closure environment any call allocates would leak forever.
    /// Resetting inside the compiled function itself (say, at `$f`'s
    /// entry) would be unsound: a non-tail self-call is an ordinary `call
    /// $f` that re-enters it from the top, and would free closures created
    /// earlier in the same top-level call that are still needed after the
    /// recursive call returns. Resetting from the host, once per top-level
    /// call, has no such hazard. `false` for a fragment that never
    /// allocates (no allocator, nothing to reset).
    pub needs_hp_reset: bool,
}

impl CompiledFragment {
    /// The module's WAT text.
    pub fn wat(&self) -> String {
        let mut w = String::new();
        for item in &self.module {
            match item {
                Item::Text(s) => w.push_str(s),
                Item::Func { header, body, .. } => {
                    w.push_str(header);
                    print_body(body, 4, &mut w);
                    w.push_str("  )\n");
                }
            }
        }
        w
    }

    /// The entry function `$f`'s body, the wrapping `Loop` included: what
    /// the gate proves, so the list proved is the list printed.
    pub fn entry(&self) -> &[Ins] {
        self.module
            .iter()
            .find_map(|item| match item {
                Item::Func { name, body, .. } if name == "f" => Some(body.as_slice()),
                _ => None,
            })
            .expect("every module has an entry function $f")
    }
}

/// One entry of `Combinators::pending`/`Combinators::kind` -- either an
/// ordinary lambda literal (`register`), or a synthesized
/// partial-application wrapper (`register_partial_app`, see its own docs
/// and `emit_pap_wrapper`). Both share the same
/// `arities`/`captures`/table-index space; this only distinguishes *how*
/// `build` treats each one once dequeued (a wrapper has no body to
/// walk).
#[derive(Clone)]
enum PendingCombinator {
    Literal(Hash),
    PartialApp { root: Hash, supplied: usize },
}

/// The registry of lambda values found while building a function.
/// `index`/`arities`/`captures`/`kind` describe every combinator
/// registered so far (in registration order, parallel to a combinator's
/// assigned index -- `captures[idx]` is that combinator's own environment
/// slot layout, from `free_vars`, meaningless for a partial-application
/// wrapper, which never reads it -- see `emit_pap_wrapper`/
/// `lower_wat`'s `Lowering::pap_env` instead; `kind[idx]` is which of the
/// two `PendingCombinator` shapes this index is); `pending` holds ones not
/// yet walked (to find what they themselves reference). `pap_index` is
/// `register_partial_app`'s own bookkeeping, kept separate from `index`
/// since a wrapper's identity (`root`, `supplied`) isn't a `Hash` at all.
///
/// `needs_generic_dispatch` is set once any function's
/// `infer_closure_arities` finds an `ArityUse::Inconsistent` entry, and
/// becomes the module's `ir::Dispatch` -- a fragment-wide decision (see
/// "Generic closure dispatch" in `lower_wat.rs`), since this compiler has
/// no real type system to locally rule out a "well-behaved" value ever
/// flowing into the one variable that isn't.
struct Combinators<'a> {
    store: &'a TermStore,
    index: HashMap<Hash, usize>,
    pending: Vec<PendingCombinator>,
    kind: Vec<PendingCombinator>,
    arities: Vec<usize>,
    captures: Vec<Vec<u32>>,
    pap_index: HashMap<(Hash, usize), usize>,
    needs_generic_dispatch: bool,
}

impl<'a> Combinators<'a> {
    fn new(store: &'a TermStore) -> Self {
        Combinators {
            store,
            index: HashMap::new(),
            pending: Vec::new(),
            kind: Vec::new(),
            arities: Vec::new(),
            captures: Vec::new(),
            pap_index: HashMap::new(),
            needs_generic_dispatch: false,
        }
    }

    /// Registers `h` (a lambda value, i.e. an `Abs`-chain -- or a named
    /// self-recursive value, an `Abs`-chain wrapped in `Rec`) if not
    /// already known, returning its assigned table index either way.
    /// `None` if `h` doesn't even peel as a nonzero-arity function (a bare
    /// closure value always takes at least one argument -- if it didn't,
    /// there'd be nothing to apply). `is_rec` isn't recorded here -- the
    /// loop in `build` re-`peel`s each pending combinator when it actually
    /// builds its body, and determines `self_idx` from
    /// that; it's only needed here, transiently, for `free_vars` to
    /// correctly exclude a self-reference from the capture list.
    fn register(&mut self, h: Hash) -> Option<usize> {
        if let Some(&i) = self.index.get(&h) {
            return Some(i);
        }
        let (arity, body, is_rec) = peel(self.store, h)?;
        if arity == 0 {
            return None;
        }
        let captures = free_vars(self.store, body, arity, is_rec);
        let idx = self.arities.len();
        self.index.insert(h, idx);
        self.arities.push(arity);
        self.captures.push(captures);
        self.kind.push(PendingCombinator::Literal(h));
        self.pending.push(PendingCombinator::Literal(h));
        Some(idx)
    }

    /// Registers a synthesized wrapper for `root` (a literal combinator,
    /// already registered at `root_idx`) applied to only `supplied` of
    /// its own `arities[root_idx]` arguments -- the compile-time
    /// desugaring of partial application (see `build_node`'s
    /// under-application handling in its `Shape::CombinatorCall` arm).
    /// `None` if this isn't actually a partial
    /// application (`supplied` is `0`, i.e. no arguments were supplied at
    /// all -- already handled as a plain value -- or `>=` `root`'s own
    /// arity -- fully saturated or over-applied, handled elsewhere).
    ///
    /// Deduplicated by `(root, supplied)` alone, *not* by the actual
    /// argument values supplied at any particular call site: the
    /// wrapper's own compiled body (`emit_pap_wrapper`) only depends on
    /// which function is being partially applied and how many of its
    /// arguments are already fixed, never on what those arguments
    /// actually evaluate to -- that happens at each creation site
    /// instead (`MakePap`, lowered by `Lowering::pap_env`), the same way any other closure's
    /// captured *values* are filled in fresh at its own creation site
    /// while its *code* is compiled once.
    fn register_partial_app(&mut self, root: Hash, root_idx: usize, supplied: usize) -> Option<usize> {
        if let Some(&idx) = self.pap_index.get(&(root, supplied)) {
            return Some(idx);
        }
        let root_arity = self.arities[root_idx];
        if supplied == 0 || supplied >= root_arity {
            return None;
        }
        let idx = self.arities.len();
        self.arities.push(root_arity - supplied);
        self.captures.push(Vec::new()); // unused by a PAP wrapper -- see struct docs
        self.pap_index.insert((root, supplied), idx);
        self.kind.push(PendingCombinator::PartialApp { root, supplied });
        self.pending.push(PendingCombinator::PartialApp { root, supplied });
        Some(idx)
    }
}

/// Builds the IR for `h` (see `ir.rs`): the whole term-analysis half of
/// compilation, with none of the representation choices. It is one walk:
/// `$f`'s body first, then every registered combinator's body, dequeued in
/// the LIFO order the registry fills, so each combinator's index (and
/// therefore its table slot) is its registration order. `None` exactly
/// where the fragment rejects a term.
pub(crate) fn build(store: &TermStore, h: Hash) -> Option<ir::Module> {
    let (arity, body, is_rec) = peel(store, h)?;
    let mut reg = Combinators::new(store);
    let entry = build_function(store, arity, body, is_rec, &[], &mut reg)?;
    let mut lifted: HashMap<usize, ir::Func> = HashMap::new();
    while let Some(pc) = reg.pending.pop() {
        // A partial-application wrapper's body is a fixed lowering
        // template; there is nothing in it to walk.
        if let PendingCombinator::Literal(h_c) = pc {
            let idx = reg.index[&h_c];
            let (c_arity, c_body, c_is_rec) = peel(store, h_c)?;
            let captures = reg.captures[idx].clone();
            let func = build_function(store, c_arity, c_body, c_is_rec, &captures, &mut reg)?;
            lifted.insert(idx, func);
        }
    }
    let combinators = reg
        .kind
        .iter()
        .enumerate()
        .map(|(idx, kind)| match kind {
            PendingCombinator::Literal(_) => ir::Combinator::Lifted(lifted.remove(&idx).expect("every registered literal was dequeued and built")),
            PendingCombinator::PartialApp { root, supplied } => ir::Combinator::Pap { root: reg.index[root], supplied: *supplied },
        })
        .collect();
    let dispatch = if reg.needs_generic_dispatch { ir::Dispatch::Curried } else { ir::Dispatch::Fast };
    Some(ir::Module { entry, combinators, dispatch })
}

/// Everything about the function being built that stays fixed across its
/// body.
struct BuildCtx<'a, 'b> {
    store: &'a TermStore,
    arity: usize,
    self_idx: Option<u32>,
    closure_arities: &'b HashMap<u32, ArityUse>,
    /// This function's environment layout (from `free_vars`): slot `j`
    /// holds the enclosing scope's relative variable `captures[j]`.
    captures: &'b [u32],
}

fn build_function(store: &TermStore, arity: usize, body: Hash, is_rec: bool, captures: &[u32], reg: &mut Combinators) -> Option<ir::Func> {
    let self_idx = is_rec.then_some(arity as u32);
    let closure_arities = infer_closure_arities(store, body, arity, self_idx)?;
    // One variable called at two arities anywhere makes the whole module
    // `Curried` (see `ir::Dispatch`).
    if closure_arities.values().any(|u| matches!(u, ArityUse::Inconsistent)) {
        reg.needs_generic_dispatch = true;
    }
    let ctx = BuildCtx { store, arity, self_idx, closure_arities: &closure_arities, captures };
    let body = build_node(&ctx, reg, body, true)?;
    Some(ir::Func { arity, is_rec, env_len: captures.len(), body })
}

fn build_args(ctx: &BuildCtx, reg: &mut Combinators, args: &[Hash]) -> Option<Vec<ir::Node>> {
    args.iter().map(|&a| build_node(ctx, reg, a, false)).collect()
}

/// One node. Sub-terms are built in the order their code is emitted, and
/// that order is combinator registration order, which is table-index
/// order (pinned by the golden WAT snapshots, `tests/golden_wat.rs`).
fn build_node(ctx: &BuildCtx, reg: &mut Combinators, h: Hash, tail: bool) -> Option<ir::Node> {
    use ir::Node;
    Some(match classify(ctx.store, h, ctx.arity, ctx.self_idx) {
        Shape::If(c, t, e) => {
            // The condition must be a direct comparison, a source op that
            // `shape::op_of` maps to a bit-result row.
            let Term::Prim(cmp, a, b) = ctx.store.resolve(c) else { return None };
            let (cmp, a, b) = (*cmp, *a, *b);
            if !is_comparison(cmp) {
                return None;
            }
            let a = build_node(ctx, reg, a, false)?;
            let b = build_node(ctx, reg, b, false)?;
            let then = build_node(ctx, reg, t, tail)?;
            let els = build_node(ctx, reg, e, tail)?;
            Node::If { cmp, a: Box::new(a), b: Box::new(b), then: Box::new(then), els: Box::new(els) }
        }
        Shape::SelfCall(args) => Node::SelfCall { args: build_args(ctx, reg, &args)?, tail },
        Shape::VarCall { var, args, .. } => {
            // Under `Consistent(k)` every call site has `k` arguments, so
            // the length check cannot fail. It stays as defence in depth:
            // a future change to arity inference cannot then silently
            // produce a `CallUnknown` with the wrong argument count.
            let expected = match ctx.closure_arities.get(&var)? {
                ArityUse::Consistent(k) => *k,
                ArityUse::Inconsistent => args.len(),
            };
            if args.len() != expected {
                return None;
            }
            let callee = Node::Read(build_read(ctx, var)?);
            Node::CallUnknown { callee: Box::new(callee), args: build_args(ctx, reg, &args)? }
        }
        Shape::CombinatorCall { root, args, .. } => {
            let idx = reg.register(root)?;
            let root_arity = reg.arities[idx];
            let captures = reg.captures[idx].clone();
            match args.len().cmp(&root_arity) {
                std::cmp::Ordering::Equal => {
                    let env = build_env(ctx, &captures)?;
                    Node::CallKnown { f: idx, env, args: build_args(ctx, reg, &args)? }
                }
                std::cmp::Ordering::Greater => {
                    // Over-application: the saturated call's result is
                    // itself called on the remaining arguments.
                    let env = build_env(ctx, &captures)?;
                    let sat = Node::CallKnown { f: idx, env, args: build_args(ctx, reg, &args[..root_arity])? };
                    let extra = build_args(ctx, reg, &args[root_arity..])?;
                    Node::CallUnknown { callee: Box::new(sat), args: extra }
                }
                std::cmp::Ordering::Less => {
                    // The wrapper is registered *before* the supplied
                    // arguments are walked, so its index comes before any combinator those
                    // arguments register.
                    let wrapper = reg.register_partial_app(root, idx, args.len())?;
                    let root_env = build_env(ctx, &captures)?;
                    Node::MakePap { wrapper, root_env, args: build_args(ctx, reg, &args)? }
                }
            }
        }
        Shape::OtherCall => return None,
        Shape::Var(i) => Node::Read(build_read(ctx, i)?),
        Shape::Lit(n) => Node::Lit(n),
        Shape::Prim(op, a, b) => {
            if is_comparison(op) {
                return None; // a comparison is only legal as an `If` condition
            }
            let a = build_node(ctx, reg, a, false)?;
            let b = build_node(ctx, reg, b, false)?;
            Node::Arith(op, Box::new(a), Box::new(b))
        }
        Shape::Combinator { .. } => {
            let idx = reg.register(h)?;
            let captures = reg.captures[idx].clone();
            Node::MakeClosure { f: idx, env: build_env(ctx, &captures)? }
        }
    })
}

/// Resolves absolute variable `v` to one of this function's parameters or
/// one of its environment slots. `None` if it is neither: out of range, or
/// this function's own self-reference used as a plain value, which the
/// fragment does not support.
fn build_read(ctx: &BuildCtx, v: u32) -> Option<ir::Read> {
    let arity = ctx.arity as u32;
    if v < arity {
        return Some(ir::Read::Param(local_index(v, ctx.arity)?));
    }
    // Must match `free_vars`'s `capture_base`: `Rec` binds the
    // self-reference at `arity`, before any real capture.
    let capture_base = if ctx.self_idx.is_some() { arity + 1 } else { arity };
    if v < capture_base {
        return None;
    }
    let rel = v - capture_base;
    let slot = ctx.captures.iter().position(|&c| c == rel)?;
    Some(ir::Read::Env(slot as u32))
}

/// The reads that fill an environment with layout `captures`. Each entry
/// is a variable of *this* scope: a lambda literal is always found at the
/// top level of the function building it, because every nested lambda is
/// lifted into a combinator of its own.
fn build_env(ctx: &BuildCtx, captures: &[u32]) -> Option<Vec<ir::Read>> {
    captures.iter().map(|&rel| build_read(ctx, rel)).collect()
}

/// A bug in an untrusted pass that the pipeline caught. Never a property of
/// the term: in debug and test builds it panics; in release the term is
/// rejected soundly (the interpreter runs it) and the bug counted, so the
/// release-mode fuzzers can assert none happened.
#[derive(Clone, Copy, Debug)]
pub enum BuilderBug {
    /// `try_compile` found the builder's IR ill-formed (`ir::check`).
    IllFormed,
    /// `try_compile` rejected a well-formed module that did not decompile
    /// back to the source term (`decompile::decompile`): a builder bug, or a
    /// false alarm in the decompiler, and either way a bug.
    Untranslated,
    /// `compile_specialised` discarded a specialisation because
    /// `spec_check::check` rejected its trace: a specialiser bug.
    BadTrace,
}

static BUILDER_BUGS: [AtomicUsize; 3] = [const { AtomicUsize::new(0) }; 3];

/// How many `kind` bugs were caught, process-wide. A process-wide counter
/// rather than a `jit` `Stats` field: `Stats` lives on one `jit::Cache` and
/// only sees calls routed through it, while fuzzers and other direct callers
/// of `try_compile` never touch a `Cache` at all.
pub fn builder_bugs(kind: BuilderBug) -> usize {
    BUILDER_BUGS[kind as usize].load(Ordering::Relaxed)
}

/// Counts a `kind` bug, and panics with `msg` in debug and test builds.
fn builder_bug(kind: BuilderBug, msg: impl FnOnce() -> String) {
    BUILDER_BUGS[kind as usize].fetch_add(1, Ordering::Relaxed);
    if cfg!(debug_assertions) {
        panic!("{}", msg());
    }
}

/// The largest term, counted as a tree, that `try_compile` compiles. The IR
/// has no `let`, so a subterm is emitted once per use, and the checker,
/// decompiler, lowering, wasmtime, sample verification and the provers
/// all walk the result: the whole JIT path costs about 0.4 s at this size,
/// doubling with it. The corpus's largest compiled term is 838 nodes
/// (`docs/related-work/` §47).
const MAX_TREE_NODES: u64 = 16_384;

/// `h`'s size as a tree (every shared subterm counted once per use), or
/// `MAX_TREE_NODES + 1` if that is larger. Linear in the DAG.
pub(crate) fn tree_size(store: &TermStore, h: Hash) -> u64 {
    let cap = MAX_TREE_NODES + 1;
    let mut size: HashMap<Hash, u64> = HashMap::new();
    // Post-order without recursion: a node is sized once its children are.
    let mut stack = vec![(h, false)];
    while let Some((u, children_done)) = stack.pop() {
        if size.contains_key(&u) {
            continue;
        }
        let kids: &[Hash] = match store.resolve(u) {
            Term::Var(_) | Term::Lit(_) => &[],
            Term::Prim(_, a, b) | Term::App(a, b) => &[*a, *b][..],
            Term::If(c, x, y) => &[*c, *x, *y][..],
            Term::Abs(b) | Term::Rec(b) => std::slice::from_ref(b),
        };
        if children_done {
            let n = kids.iter().fold(1, |n: u64, k| n.saturating_add(size[k]));
            size.insert(u, n.min(cap));
        } else {
            stack.push((u, true));
            stack.extend(kids.iter().map(|&k| (k, false)));
        }
    }
    size[&h]
}

/// Try to compile `h` as an `arity`-ary numeric function (or, for `arity`
/// `0`, a single closed expression to evaluate once). Returns `None` if
/// `h` (or any combinator value it uses) falls outside the compilable
/// fragment, or is larger as a tree than `MAX_TREE_NODES`: the interpreter
/// runs those. Every accepted module has been decompiled back to `h`.
pub fn try_compile(store: &TermStore, h: Hash) -> Option<CompiledFragment> {
    if tree_size(store, h) > MAX_TREE_NODES {
        return None;
    }
    let m = build(store, h)?;
    if let Err(e) = ir::check(&m) {
        builder_bug(BuilderBug::IllFormed, || format!("the IR builder produced an ill-formed module for {h:?}: {e}"));
        return None;
    }
    // Translation validation: the IR must mean exactly `h`, up to a
    // `Dispatch::Fast` arity trap (a `call_indirect` type mismatch on a
    // closure applied at the wrong arity) -- a real runtime distinction the
    // term semantics doesn't model as separate from ordinary evaluation.
    // `jit.rs` doesn't install such a fragment: the kernel types closures by
    // exact arity, so it gets no universal proof (`docs/related-work/` §40).
    // Sample verification alone would miss one reached only off-sample.
    // A mismatch here is a builder bug like an ill-formed module.
    if crate::verify::decompile::decompile(&m, &mut TermStore::new()) != Some(h) {
        builder_bug(BuilderBug::Untranslated, || format!("the IR for {h:?} failed translation validation: it does not decompile back to the source term"));
        return None;
    }
    Some(crate::jit::lower_wat::lower(&m))
}

/// What `compile_specialised` compiled.
pub struct Compiled {
    pub frag: CompiledFragment,
    /// `Some((store, h'))` when the fragment was compiled from `h'`, a
    /// specialisation of `h` that `spec_check::check` accepted. `None` when
    /// it was compiled from `h` itself.
    pub specialised: Option<(TermStore, Hash)>,
}

/// The one pipeline driver: specialise `h` (`specialise.rs`, untrusted),
/// check the certificate (`spec_check.rs`, trusted and independent), and
/// compile the result with `try_compile`. The passes stay separate:
/// `try_compile` is a pure translation whose module decompiles to exactly
/// the term it was given. This function adds only the certificate-checked
/// step from `h` to that term. If the specialised term does not compile,
/// `h` is tried instead.
///
/// The claim for a specialised result: its module decompiles to `h'`, and
/// `h' ≡ h` by a checked βv trace. That equivalence is not kernel-checked
/// (docs/related-work/ §37).
pub fn compile_specialised(store: &TermStore, h: Hash) -> Option<Compiled> {
    compile_candidate(store, h, crate::jit::specialise::specialise(store, h))
}

fn compile_candidate(store: &TermStore, h: Hash, sp: crate::jit::specialise::Specialised) -> Option<Compiled> {
    if !sp.trace.is_empty() {
        match crate::verify::spec_check::check(store, h, &sp.trace, sp.term) {
            // `sp.store` is the specialiser's, but it can't lie about
            // `sp.term`: a store's hashes are the content hashes of what it
            // holds, and the checker accepted that hash.
            Ok(()) => {
                if let Some(frag) = try_compile(&sp.store, sp.term) {
                    return Some(Compiled { frag, specialised: Some((sp.store, sp.term)) });
                }
            }
            Err(e) => builder_bug(BuilderBug::BadTrace, || {
                format!("the specialiser produced a trace the checker rejects for {h:?}: step {}: {}", e.step, e.reason)
            }),
        }
    }
    try_compile(store, h).map(|frag| Compiled { frag, specialised: None })
}

#[cfg(test)]
mod tests;
