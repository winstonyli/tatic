//! Builders over `Globals`: `Postulates` (assumed constants and parameter scopes) and `NatPostulates` (a postulated
//! Bool/Nat construction). Nothing here is read by the checker; a term built with it is checked like any other. A child
//! module of `kernel` so it keeps access to the private fields of `Globals` and `Ctx`.

use super::*;

/// Builds a context of *postulated* (assumed) constants: pushes a type and
/// returns a handle that can be resolved, at any later point while still
/// building on the same context, to the reference that correctly refers to
/// it. `globals` only grows -- nothing ever truncates it -- so `Const(pos)`
/// is stable regardless of how many more postulates get pushed afterward, or
/// how many builder scopes open and close around it.
///
/// Used instead of trying to derive base types like Bool/Nat/Int from
/// nothing. That turns out to be a real dead end, not just tedium: any
/// "vacuous eliminator" for an empty/base case needs a witness-extractor
/// shaped like `Pi x : Sort(m). x`, but that type itself only exists at
/// `Sort(m+1)` — one universe *above* what it can extract into — so it can
/// never eliminate into its own level. Predicativity is correctly refusing
/// what would otherwise be a disguised `Type : Type`. Real kernels sidestep
/// this by taking a small base type as primitive (or, as here, postulated).
///
/// A postulate is referred to by `Const(level)` and checked as one of the
/// kernel's `Globals` (`RELATED_WORK.md` §69).
///
/// A scope's parameters (`bind`) are `Free(level)`s, which no push shifts.
/// Levels come from a counter that never reuses one, so a `Free` that
/// escapes its scope can't be bound by a later scope's `close` and is
/// rejected by the kernel instead (`RELATED_WORK.md` §70).
///
/// A `push` may happen inside an open scope: it adds a global, which that
/// scope's `close` doesn't wrap. Its type must be closed, so a scope's own
/// entry, whose type mentions a parameter, can't be pushed by mistake;
/// bind it.
#[derive(Clone)]
pub struct Postulates {
    pub globals: Globals,
    /// The live parameters' `Free` levels and types, in increasing level
    /// order. A type may mention earlier parameters as `Free`s.
    pub(super) params: Vec<(u32, Expr)>,
    /// The next `Free` level `bind` hands out. Never lowered.
    pub(super) next_free: u32,
    /// How many scopes are open.
    pub(super) scopes: u32,
}

/// A builder scope from `Postulates::open` to `close` or `abandon`.
#[must_use]
pub struct Scope {
    /// How many parameters were live (`params.len()`) when this scope
    /// opened: `close`/`abandon` roll `params` back to here.
    params_len: usize,
    /// The first `Free` level this scope can hand out: every level handed
    /// out before this scope opened is below it.
    first: u32,
    /// How many scopes were already open when this one opened
    /// (`Postulates::scopes` before `open` incremented it). `close` and
    /// `abandon` assert only the innermost scope (`self.scopes == depth +
    /// 1`) is closing, so scopes must close innermost-first.
    depth: u32,
}

/// `abstract_frees`' memo for one set of `levels`: a shared node's result
/// by pointer and depth.
type FreesMemo = HashMap<(PtrKey, u32), Rc<Expr>>;

/// Under `d` binders of `e`, `Free(levels[j])` becomes the `Var` for the
/// `j`-th of `levels.len()` binders wrapped outside `e`, outermost
/// first. A `Free` not in `levels` (an enclosing scope's, or one that
/// escaped a closed scope) is left for the final check to reject.
///
/// Builder-side, not trusted: the kernel checks what `close` builds. It
/// mirrors `shift`, with `free` in place of `loose` for the skip test,
/// since every level in `levels` is at least `first`.
fn abstract_frees(e: &Expr, first: u32, levels: &[u32], d: u32) -> Expr {
    abstract_frees_in(e, first, levels, d, &mut FreesMemo::new())
}

/// `abstract_frees` with a memo shared across calls for the same
/// `levels`. A node referenced from more than one place is memoised by
/// pointer and depth, as `infer_rc` does, so a shared subterm is walked
/// once and its result stays shared. Unmemoised, a doubling DAG is walked
/// as the tree it unfolds to, and the copy loses the sharing `infer`'s
/// memo relies on (`RELATED_WORK.md` §63).
fn abstract_frees_in(e: &Expr, first: u32, levels: &[u32], d: u32, memo: &mut FreesMemo) -> Expr {
    if free_of(e) <= first {
        return e.clone();
    }
    let mut go = |x: &Rc<Expr>, d: u32| {
        if x.free() <= first {
            return x.clone();
        }
        if Rc::strong_count(x) == 1 {
            return hc::intern_new(abstract_frees_in(x, first, levels, d, memo));
        }
        let key = (PtrKey(x.clone()), d);
        if let Some(r) = memo.get(&key) {
            return r.clone();
        }
        let r = hc::intern_new(abstract_frees_in(x, first, levels, d, memo));
        memo.insert(key, r.clone());
        r
    };
    grow(|| match e {
        Expr::Free(l) => match levels.binary_search(l) {
            Ok(j) => Expr::Var(d + (levels.len() - 1 - j) as u32),
            Err(_) => Expr::Free(*l),
        },
        Expr::Var(k) => Expr::Var(*k),
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Const(l) => Expr::Const(*l),
        Expr::Pi(a, b) => Expr::Pi(go(a, d), go(b, d + 1)),
        Expr::Lam(a, b) => Expr::Lam(go(a, d), go(b, d + 1)),
        Expr::App(f, a) => Expr::App(go(f, d), go(a, d)),
        Expr::Id(a, x, y) => Expr::Id(go(a, d), go(x, d), go(y, d)),
        Expr::Refl(a) => Expr::Refl(go(a, d)),
        Expr::J { motive, base, a, b, p } => Expr::J {
            motive: go(motive, d),
            base: go(base, d),
            a: go(a, d),
            b: go(b, d),
            p: go(p, d),
        },
        Expr::W(a, b) => Expr::W(go(a, d), go(b, d + 1)),
        Expr::Sup(a, f) => Expr::Sup(go(a, d), go(f, d)),
        Expr::WRec { motive, children_ty, step, target } => Expr::WRec {
            motive: go(motive, d),
            children_ty: go(children_ty, d + 1),
            step: go(step, d),
            target: go(target, d),
        },
        Expr::Sigma(a, b) => Expr::Sigma(go(a, d), go(b, d + 1)),
        Expr::Pair(fam, a, b) => Expr::Pair(go(fam, d + 1), go(a, d), go(b, d)),
        Expr::SigRec { motive, step, target } => Expr::SigRec {
            motive: go(motive, d),
            step: go(step, d),
            target: go(target, d),
        },
    })
}

/// Which binders `Postulates::close` wraps: `Pi` to build a type that
/// quantifies over the scope's entries, `Lam` for a value of that type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Binder {
    Pi,
    Lam,
}

impl Postulates {
    pub fn new() -> Self {
        Postulates { globals: Globals::new(), params: Vec::new(), next_free: 0, scopes: 0 }
    }
    pub fn push(&mut self, ty: Expr) -> usize {
        let pos = self.globals.len();
        assert!(loose_of(&ty) == 0 && free_of(&ty) == 0, "a postulate's type must be closed: {ty:?}");
        // RELATED_WORK §68: an ill-formed entry sat in the context unchecked
        // until a claim that used it failed. This also catches a postulate
        // referencing itself or a later one: `infer` checks it against
        // `self.globals` as it stands before this push, so a forward
        // `Const` fails in `const_type` with "unknown constant".
        if let Err(err) = self.infer(&ty).and_then(|t| expect_sort(&t).map(|_| ())) {
            panic!("a postulate's type isn't a type: {err}\n  type: {ty:?}");
        }
        self.globals.push_back(ty);
        pos
    }
    pub fn get(&self, pos: usize) -> Expr {
        Expr::Const(pos as u32)
    }
    /// Opens a builder scope: parameters bound after this point (`bind`)
    /// belong to it until `close` or `abandon`.
    pub fn open(&mut self) -> Scope {
        let s = Scope { params_len: self.params.len(), first: self.next_free, depth: self.scopes };
        self.scopes += 1;
        s
    }
    /// Adds a parameter of type `ty` to the innermost open scope and
    /// returns it as a fresh `Free` level. `ty` may mention the live
    /// parameters, and is checked to be a type. Panics outside a scope.
    pub fn bind(&mut self, ty: Expr) -> Expr {
        assert!(self.scopes > 0, "bind outside a scope");
        if let Err(err) = self.infer_open(&ty).and_then(|t| expect_sort(&t).map(|_| ())) {
            panic!("a parameter's type isn't a type: {err}\n  type: {ty:?}");
        }
        let l = self.next_free;
        self.next_free = l.checked_add(1).expect("Free levels ran out");
        self.params.push((l, ty));
        Expr::Free(l)
    }
    /// Wraps a binder around `body` for each parameter bound since `s` was
    /// opened, outermost first, then rolls them back. A scope that bound
    /// nothing returns `body` unchanged.
    pub fn close(&mut self, s: Scope, binder: Binder, body: Expr) -> Expr {
        assert!(self.scopes == s.depth + 1, "scopes must close innermost-first");
        // A loose `Var` here would be captured by the new binders: it's a
        // sign a scope local escaped `bind`.
        assert!(loose_of(&body) == 0, "close's body has a loose Var: a scope local escaped bind (RELATED_WORK §70)");
        let levels: Vec<u32> = self.params[s.params_len..].iter().map(|(l, _)| *l).collect();
        let mut acc = abstract_frees(&body, s.first, &levels, 0);
        for i in (0..levels.len()).rev() {
            let dom = abstract_frees(&self.params[s.params_len + i].1, s.first, &levels[..i], 0);
            acc = match binder {
                Binder::Pi => pi(dom, acc),
                Binder::Lam => lam(dom, acc),
            };
        }
        self.abandon(s);
        acc
    }
    /// Rolls back what was bound since `s` was opened, closing nothing (for
    /// a build that gave up). `next_free` stays where it is, so no level is
    /// handed out twice (`RELATED_WORK.md` §67).
    pub fn abandon(&mut self, s: Scope) {
        assert!(self.scopes == s.depth + 1, "scopes must close innermost-first");
        self.params.truncate(s.params_len);
        self.scopes = self.scopes.checked_sub(1).expect("scopes underflow");
    }
    pub fn check(&self, e: &Expr, ty: &Expr) -> Result<(), String> {
        check_in(&self.globals, &Ctx::new(), e, ty)
    }
    pub fn infer(&self, e: &Expr) -> Result<Expr, String> {
        infer_in(&self.globals, &Ctx::new(), e)
    }
    /// The globals, a local context of the live parameters' types, and
    /// their levels, for checking a term that mentions them: each
    /// parameter becomes the `Var` for its entry.
    fn open_ctx(&self) -> (Globals, Ctx, Vec<u32>) {
        let levels: Vec<u32> = self.params.iter().map(|(l, _)| *l).collect();
        let locals = self.params.iter().enumerate().map(|(i, (_, ty))| abstract_frees(ty, 0, &levels[..i], 0)).collect();
        (self.globals.clone(), locals, levels)
    }
    /// `check` for a term and type that may mention the live parameters.
    pub fn check_open(&self, e: &Expr, ty: &Expr) -> Result<(), String> {
        // A loose `Var` would be read as one of the parameters.
        assert!(loose_of(e) == 0 && loose_of(ty) == 0, "check_open on a term or type with a loose Var: {e:?} : {ty:?}");
        let (g, l, levels) = self.open_ctx();
        let mut memo = FreesMemo::new();
        let e = abstract_frees_in(e, 0, &levels, 0, &mut memo);
        let ty = abstract_frees_in(ty, 0, &levels, 0, &mut memo);
        check_in(&g, &l, &e, &ty)
    }
    /// `infer` for a term that may mention the live parameters. The type
    /// it returns mentions them as `Var`s, not `Free`s, so it's only for
    /// uses like `expect_sort` that don't put it back into a term.
    pub fn infer_open(&self, e: &Expr) -> Result<Expr, String> {
        assert!(loose_of(e) == 0, "infer_open on a term with a loose Var: {e:?}");
        let (g, l, levels) = self.open_ctx();
        infer_in(&g, &l, &abstract_frees(e, 0, &levels, 0))
    }
}
impl Default for Postulates {
    fn default() -> Self {
        Self::new()
    }
}

// --- reusable proof-term builders ---------------------------------------
//
// Generic lemmas, built once via `J`, for composing equality proofs.
// Not yet used by the straight-line proof in `proof.rs` (that fragment's
// correctness happens to hold by `refl` alone), but they're exactly the
// building blocks an inductive proof of the tail-call-to-loop compilation
// (a genuinely nontrivial equivalence) will need, so they belong here as
// kernel infrastructure rather than being reinvented ad hoc later.

/// `sym a_ty x y p : Id(A, y, x)`, given `p : Id(A, x, y)` -- propositional
/// symmetry of equality.
pub fn sym(a_ty: &Expr, x: &Expr, y: &Expr, p: Expr) -> Expr {
    // motive(x', y', _) := Id(A, y', x')
    let motive = lam(
        a_ty.clone(),
        lam(
            shift(a_ty, 0, 1),
            lam(
                id(shift(a_ty, 0, 2), var(1), var(0)),
                id(shift(a_ty, 0, 3), var(1), var(2)),
            ),
        ),
    );
    let base = lam(a_ty.clone(), refl(var(0)));
    jelim(motive, base, x.clone(), y.clone(), p)
}

/// `transport sort_k a_ty b_ty p x : b_ty`, given `p : Id(Sort(sort_k),
/// a_ty, b_ty)` and `x : a_ty` -- moves an element from one type to a
/// propositionally equal one (`a_ty`/`b_ty` themselves, as *elements* of
/// `Sort(sort_k)`), the standard operation `J` derives (sometimes called
/// `subst`). Built via `J`'s motive `\A B:Sort(k). \_:Id(Sort(k),A,B). A ->
/// B`, whose base case (`p` a `Refl`) is the identity function.
pub fn transport(sort_k: u32, a_ty: Expr, b_ty: Expr, p: Expr, x: Expr) -> Expr {
    let motive = lam(
        sort(sort_k),
        lam(
            sort(sort_k),
            lam(id(sort(sort_k), var(1), var(0)), arrow(var(2), var(1))),
        ),
    );
    let base = lam(sort(sort_k), lam(var(0), var(0)));
    app(jelim(motive, base, a_ty, b_ty, p), x)
}

/// `cong1 f a b p : Id(B, f a, f b)`, given `p : Id(A, a, b)` and `f : A ->
/// B`. Congruence for a unary function -- applying the same function to
/// equal arguments gives equal results, regardless of what `f` itself
/// computes. `b_ty` is `f`'s codomain, independent of `a_ty` (its domain);
/// callers where `f : A -> A` may pass the same `Expr` for both.
pub fn cong1(a_ty: &Expr, b_ty: &Expr, f: &Expr, a: Expr, b: Expr, p: Expr) -> Expr {
    cong1_in(&ShiftMemo::default(), a_ty, b_ty, f, a, b, p)
}

fn cong1_in(memo: &ShiftMemo, a_ty: &Expr, b_ty: &Expr, f: &Expr, a: Expr, b: Expr, p: Expr) -> Expr {
    let shift = |e: &Expr, c: u32, n: i32| shift_memo(e, c, n, memo);
    // motive(a', b', _) := Id(B, f a', f b')
    let motive = lam(
        a_ty.clone(),
        lam(
            shift(a_ty, 0, 1),
            lam(
                id(shift(a_ty, 0, 2), var(1), var(0)),
                id(
                    shift(b_ty, 0, 3),
                    app(shift(f, 0, 3), var(2)),
                    app(shift(f, 0, 3), var(1)),
                ),
            ),
        ),
    );
    let base = lam(a_ty.clone(), refl(app(shift(f, 0, 1), var(0))));
    jelim(motive, base, a, b, p)
}

/// `trans a_ty x y z p1 p2 : Id(A, x, z)`, given `p1 : Id(A,x,y)` and
/// `p2 : Id(A,y,z)`. `a_ty`/`x` must be valid in the same context as
/// `p1`/`p2` (they are held fixed while eliminating on `p2`).
pub fn trans_proof(a_ty: &Expr, x: &Expr, y: &Expr, z: &Expr, p1: Expr, p2: Expr) -> Expr {
    trans_proof_in(&ShiftMemo::default(), a_ty, x, y, z, p1, p2)
}

fn trans_proof_in(memo: &ShiftMemo, a_ty: &Expr, x: &Expr, y: &Expr, z: &Expr, p1: Expr, p2: Expr) -> Expr {
    let shift = |e: &Expr, c: u32, n: i32| shift_memo(e, c, n, memo);
    // `arrow`, with its codomain shifted through the memo (a plain `shift` copies the shifted `x`
    // afresh at every call).
    let arrow = |a: Expr, b: Expr| pi(a, shift(&b, 0, 1));
    // motive(y', z', _) := Id(A, x, y') -> Id(A, x, z')
    let motive = lam(
        a_ty.clone(),
        lam(
            shift(a_ty, 0, 1),
            lam(
                id(shift(a_ty, 0, 2), shift(x, 0, 2), var(1)),
                arrow(
                    id(shift(a_ty, 0, 3), shift(x, 0, 3), var(2)),
                    id(shift(a_ty, 0, 3), shift(x, 0, 3), var(1)),
                ),
            ),
        ),
    );
    let base = lam(
        a_ty.clone(),
        lam(id(shift(a_ty, 0, 1), shift(x, 0, 1), var(0)), var(0)),
    );
    app(jelim(motive, base, y.clone(), z.clone(), p2), p1)
}

/// `cong_n a_ty b_ty f xs ys ps : Id(B, f x_0 .. x_{n-1}, f y_0 .. y_{n-1})`,
/// given `ps[i] : Id(A, xs[i], ys[i])` for each `i` -- congruence for a
/// function of `n` arguments (all of type `A`, result type `B`), built by
/// rewriting one argument at a time (`cong1` on the partial application
/// with that argument's position held open as a fresh binder) and chaining
/// the `n` resulting steps with `trans_proof`. `n == 1` reduces to `cong1`
/// itself (up to an eta-expansion `cong1` doesn't need); `n == 0` is `refl`.
pub fn cong_n(a_ty: &Expr, b_ty: &Expr, f: &Expr, xs: &[Expr], ys: &[Expr], ps: Vec<Expr>) -> Expr {
    assert_eq!(xs.len(), ys.len());
    assert_eq!(xs.len(), ps.len());
    let memo = ShiftMemo::default();
    let shift = |e: &Expr, c: u32, n: i32| shift_memo(e, c, n, &memo);
    let apply = |args: &[Expr]| -> Expr { args.iter().cloned().fold(f.clone(), app) };
    let lhs_all = apply(xs);
    if xs.is_empty() {
        return refl(lhs_all);
    }

    let mut cur_args: Vec<Expr> = xs.to_vec();
    let mut acc: Option<(Expr, Expr)> = None; // (running proof, its right-hand value)
    for i in 0..xs.len() {
        // g := \z. f cur_args[0] .. cur_args[i-1] z cur_args[i+1] ..,
        // built fresh under one new binder, so every other (already-fixed)
        // argument needs reindexing by the binder `g` itself introduces.
        let g_body = cur_args.iter().enumerate().fold(shift(f, 0, 1), |acc, (j, a)| {
            app(acc, if j == i { var(0) } else { shift(a, 0, 1) })
        });
        let g = lam(a_ty.clone(), g_body);
        // `g` is `f` with every position but `i` already filled in -- a
        // *full* application under one open binder, not a curried partial
        // one, so its codomain is `f`'s own full result type `b_ty`
        // regardless of `i`.
        let step = cong1_in(&memo, a_ty, b_ty, &g, cur_args[i].clone(), ys[i].clone(), ps[i].clone());
        cur_args[i] = ys[i].clone();
        let after = apply(&cur_args);
        acc = Some(match acc {
            None => (step, after),
            Some((prev, mid)) => (trans_proof_in(&memo, b_ty, &lhs_all, &mid, &after, prev, step), after),
        });
    }
    acc.unwrap().0
}

/// `Pi C:(Bool->Sort0). Pi ct:C(true). Pi cf:C(false). <body_d3>`, where
/// `body_d3` must already be built assuming exactly this three-binder
/// depth (`C=Var2, ct=Var1, cf=Var0`) relative to `bool_ref`/`true_ref`/
/// `false_ref`'s own (shared) ambient depth -- the shared shape
/// `bool_rec`'s own type and both its computation-rule axioms all need,
/// differing only in what comes after the three binders.
fn wrap_c_ct_cf(bool_ref: &Expr, true_ref: &Expr, false_ref: &Expr, body_d3: Expr) -> Expr {
    let c_ty = arrow(bool_ref.clone(), sort(0));
    let true_d1 = shift(true_ref, 0, 1);
    let false_d2 = shift(false_ref, 0, 2);
    let pi_cf = pi(app(var(1), false_d2), body_d3);
    let pi_ct = pi(app(var(0), true_d1), pi_cf);
    pi(c_ty, pi_ct)
}

/// A real, computing `Nat` built from this kernel's own existing four
/// primitives alone (`Pi`/`Lam`/`Id`/`W`, plus `Postulates` for the base
/// types a predicative kernel can't derive from nothing) -- the reusable
/// form of `tests::nat_via_w_is_a_genuinely_computing_inductive_type`'s
/// own construction. See that test's doc comment for the full
/// derivation, including the induction-hypothesis-closure typing gap
/// `WRec`'s own `children_ty` field (see `Expr::WRec`'s own doc) closes.
/// `proof.rs`'s own `Ev`/`ev_rec` methodology -- postulate the
/// recursor's existence *and* separately postulate each leaf's own
/// computation rule as an explicit axiom, never relying on any
/// underlying automatic reduction -- remains the right shape for an
/// *indexed* family like `Ev(params, v)` regardless of that fix, since
/// this `Nat`'s own plain structural recursor doesn't eliminate for an
/// indexed family either way. Reusing this construction elsewhere
/// therefore saves inventing a *new* postulated base type per use site,
/// not that per-leaf axiom discipline itself.
///
/// Exposes postulate *positions*, not resolved `Expr`s: every accessor
/// below recomputes its result fresh from `p: &Postulates` at call time,
/// the same discipline `Postulates::get` itself follows (see its own
/// doc). This isn't just style -- it's what lets `nat_ty`/`zero`/`succ`
/// stay correct no matter how many further postulates get pushed onto
/// the same `Postulates` in between two calls, sidestepping by
/// construction the exact class of manual-reshifting bug the original,
/// self-contained test needed a hand-written `shift` to work around once
/// (a value built once, then reused unchanged after a later `p.push`,
/// silently ends up referencing the wrong postulate).
#[derive(Clone, Copy)]
pub struct NatPostulates {
    pub bool_pos: usize,
    pub true_pos: usize,
    pub false_pos: usize,
    pub unit_pos: usize,
    pub star_pos: usize,
    pub empty_pos: usize,
    pub empty_elim_pos: usize,
    pub child_ty_pos: usize,
    pub child_ty_true_eq_pos: usize,
    pub child_ty_false_eq_pos: usize,
    pub bool_rec_pos: usize,
    pub bool_rec_true_eq_pos: usize,
    pub bool_rec_false_eq_pos: usize,
}
impl NatPostulates {
    /// Pushes every postulate this construction needs onto `p`, in
    /// order. Call once per `Postulates`; every other method just
    /// resolves fresh against the positions stored here.
    pub fn new(p: &mut Postulates) -> Self {
        let bool_pos = p.push(sort(0));
        let true_pos = p.push(p.get(bool_pos));
        let false_pos = p.push(p.get(bool_pos));
        let unit_pos = p.push(sort(0));
        let star_pos = p.push(p.get(unit_pos));
        let empty_pos = p.push(sort(0));
        let empty_elim_pos = p.push(pi(sort(0), arrow(shift(&p.get(empty_pos), 0, 1), var(0))));
        let child_ty_pos = p.push(arrow(p.get(bool_pos), sort(0)));
        let child_ty_true_eq_pos = p.push(id(sort(0), app(p.get(child_ty_pos), p.get(true_pos)), p.get(unit_pos)));
        let child_ty_false_eq_pos = p.push(id(sort(0), app(p.get(child_ty_pos), p.get(false_pos)), p.get(empty_pos)));

        // bool_rec : Pi C:(Bool->Sort0). C(true) -> C(false) -> Pi b:Bool. C(b)
        let bool_rec_body_d3 = pi(shift(&p.get(bool_pos), 0, 3), app(var(3), var(0)));
        let bool_rec_ty = wrap_c_ct_cf(&p.get(bool_pos), &p.get(true_pos), &p.get(false_pos), bool_rec_body_d3);
        let bool_rec_pos = p.push(bool_rec_ty);

        // bool_rec_true_eq : Pi C ct cf. Id(C(true), bool_rec(C,ct,cf)(true), ct)
        let true_d3 = shift(&p.get(true_pos), 0, 3);
        let applied_d3 = app(app(app(shift(&p.get(bool_rec_pos), 0, 3), var(2)), var(1)), var(0));
        let true_eq_body_d3 = id(app(var(2), true_d3.clone()), app(applied_d3, true_d3), var(1));
        let bool_rec_true_eq_ty = wrap_c_ct_cf(&p.get(bool_pos), &p.get(true_pos), &p.get(false_pos), true_eq_body_d3);
        let bool_rec_true_eq_pos = p.push(bool_rec_true_eq_ty);

        // bool_rec_false_eq : Pi C ct cf. Id(C(false), bool_rec(C,ct,cf)(false), cf)
        let false_d3 = shift(&p.get(false_pos), 0, 3);
        let applied_d3b = app(app(app(shift(&p.get(bool_rec_pos), 0, 3), var(2)), var(1)), var(0));
        let false_eq_body_d3 = id(app(var(2), false_d3.clone()), app(applied_d3b, false_d3), var(0));
        let bool_rec_false_eq_ty = wrap_c_ct_cf(&p.get(bool_pos), &p.get(true_pos), &p.get(false_pos), false_eq_body_d3);
        let bool_rec_false_eq_pos = p.push(bool_rec_false_eq_ty);

        NatPostulates {
            bool_pos,
            true_pos,
            false_pos,
            unit_pos,
            star_pos,
            empty_pos,
            empty_elim_pos,
            child_ty_pos,
            child_ty_true_eq_pos,
            child_ty_false_eq_pos,
            bool_rec_pos,
            bool_rec_true_eq_pos,
            bool_rec_false_eq_pos,
        }
    }

    pub fn bool_ty(&self, p: &Postulates) -> Expr {
        p.get(self.bool_pos)
    }
    pub fn true_(&self, p: &Postulates) -> Expr {
        p.get(self.true_pos)
    }
    pub fn false_(&self, p: &Postulates) -> Expr {
        p.get(self.false_pos)
    }
    pub fn unit_ty(&self, p: &Postulates) -> Expr {
        p.get(self.unit_pos)
    }
    pub fn star(&self, p: &Postulates) -> Expr {
        p.get(self.star_pos)
    }
    pub fn empty_ty(&self, p: &Postulates) -> Expr {
        p.get(self.empty_pos)
    }
    /// `ChildTy(b)`.
    pub fn child_ty(&self, p: &Postulates, b: Expr) -> Expr {
        app(p.get(self.child_ty_pos), b)
    }
    /// The raw, uninstantiated `bool_rec : Pi C ct cf. Pi b:Bool. C(b)`.
    pub fn bool_rec(&self, p: &Postulates) -> Expr {
        p.get(self.bool_rec_pos)
    }
    /// The raw, uninstantiated `bool_rec_true_eq` computation-rule axiom.
    pub fn bool_rec_true_eq(&self, p: &Postulates) -> Expr {
        p.get(self.bool_rec_true_eq_pos)
    }
    /// The raw, uninstantiated `bool_rec_false_eq` computation-rule axiom.
    pub fn bool_rec_false_eq(&self, p: &Postulates) -> Expr {
        p.get(self.bool_rec_false_eq_pos)
    }

    /// `Nat := W(Bool, ChildTy) : Sort(0)`.
    pub fn nat_ty(&self, p: &Postulates) -> Expr {
        wty(p.get(self.bool_pos), app(shift(&p.get(self.child_ty_pos), 0, 1), var(0)))
    }

    /// `Zero : Nat`, transported from `empty_elim(Nat) : Empty -> Nat`
    /// along `child_ty_false_eq`.
    pub fn zero(&self, p: &Postulates) -> Expr {
        sup(p.get(self.false_pos), self.zero_child_fn(p))
    }

    /// `f_zero : ChildTy(false) -> Nat`, `Zero`'s own child function --
    /// exposed separately from `zero` because it's exactly the shape
    /// `WRec`'s own automatic reduction needs an induction-hypothesis
    /// closure to have (see `tests::nat_via_w_is_a_genuinely_computing_inductive_type`,
    /// which uses this to rebuild and typecheck that closure by hand).
    pub fn zero_child_fn(&self, p: &Postulates) -> Expr {
        let nat_ty = self.nat_ty(p);
        let f_empty_nat = app(p.get(self.empty_elim_pos), nat_ty.clone());
        let arrow_nat_fn = lam(sort(0), arrow(var(0), shift(&nat_ty, 0, 1)));
        let cong_false = cong1(
            &sort(0),
            &sort(0),
            &arrow_nat_fn,
            app(p.get(self.child_ty_pos), p.get(self.false_pos)),
            p.get(self.empty_pos),
            p.get(self.child_ty_false_eq_pos),
        );
        let sym_cong_false = sym(
            &sort(0),
            &arrow(app(p.get(self.child_ty_pos), p.get(self.false_pos)), nat_ty.clone()),
            &arrow(p.get(self.empty_pos), nat_ty.clone()),
            cong_false,
        );
        transport(
            0,
            arrow(p.get(self.empty_pos), nat_ty.clone()),
            arrow(app(p.get(self.child_ty_pos), p.get(self.false_pos)), nat_ty.clone()),
            sym_cong_false,
            f_empty_nat,
        )
    }

    /// `Succ(pred) : Nat`, given `pred : Nat` already valid in the
    /// caller's *current* context (e.g. `p.get` of a just-pushed
    /// postulate, or a local variable under whatever binders are
    /// ambient at the call site) -- transported from `(\_:Unit. pred) :
    /// Unit -> Nat` along `child_ty_true_eq`.
    pub fn succ(&self, p: &Postulates, pred: Expr) -> Expr {
        let nat_ty = self.nat_ty(p);
        let f_unit_nat = lam(p.get(self.unit_pos), shift(&pred, 0, 1));
        let arrow_nat_fn = lam(sort(0), arrow(var(0), shift(&nat_ty, 0, 1)));
        let cong_true = cong1(
            &sort(0),
            &sort(0),
            &arrow_nat_fn,
            app(p.get(self.child_ty_pos), p.get(self.true_pos)),
            p.get(self.unit_pos),
            p.get(self.child_ty_true_eq_pos),
        );
        let sym_cong_true = sym(
            &sort(0),
            &arrow(app(p.get(self.child_ty_pos), p.get(self.true_pos)), nat_ty.clone()),
            &arrow(p.get(self.unit_pos), nat_ty.clone()),
            cong_true,
        );
        let f_succ = transport(
            0,
            arrow(p.get(self.unit_pos), nat_ty.clone()),
            arrow(app(p.get(self.child_ty_pos), p.get(self.true_pos)), nat_ty.clone()),
            sym_cong_true,
            f_unit_nat,
        );
        sup(p.get(self.true_pos), f_succ)
    }
}
