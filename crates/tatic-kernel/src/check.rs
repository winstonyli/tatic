use super::*;

/// `infer`'s own `Sup` arm's error-message formatting, out of line and
/// `#[cold]` -- an error path, kept off `infer`'s hot frame (see
/// `infer_sigma`).
#[cold]
#[inline(never)]
fn sup_codomain_depends_on_own_argument(cod_nf: &Expr) -> String {
    format!("sup: children function's codomain must not depend on its own argument: {}", brief(cod_nf))
}

/// The error for a `Free` reaching the type checker, out of line and
/// `#[cold]` (see `infer_sigma`).
#[cold]
#[inline(never)]
fn free_escaped(l: u32) -> String {
    format!("free parameter ${l} escaped its scope")
}

// --- reduction ------------------------------------------------------------
//
// `whnf`/`nf` are memoized by node for the whole region (`hc`'s memos). This
// is sound regardless of typing context, since reduction never consults one
// -- unlike a cache for `infer`/`check` themselves, which must be keyed on
// more than the node (the same subterm can mean different things under
// different contexts; see `InferCache`).

/// A context id's innermost binder, for [`InferCache`]. A binder with no type of the term (`fresh`)
/// has no type recorded and loose range `u32::MAX`; it and the caller's context 0 have `run` 0.
#[derive(Clone, Copy, Default)]
pub(super) struct CtxBinder {
    pub(super) parent: u32,
    ty: Option<Key>,
    /// The type's loose range.
    pub(super) loose: u32,
    /// How many binders with a type of the term this context ends with, itself included.
    pub(super) run: u32,
    /// An ancestor at most `run` binders out (itself when `run` is 0), from which
    /// [`InferCache::skip`] climbs a run in O(log) steps: Myers' skew-binary jump pointers.
    pub(super) jump: u32,
}

/// `infer`'s memo for one public `infer` or `check` call (`docs/related-work/`
/// §63). A context is named by an id: 0 is the caller's, and entering a
/// binder whose type is the node `a` from context `cid` gives the id
/// interned for `(cid, a)`. Equal ids then mean the same sequence of binder
/// types, which, with the node, is all `infer`'s answer depends on within
/// one call -- it also depends on `g` and the caller's context, but that's
/// sound because the cache is empty when a call starts and emptied when it
/// ends ([`with_infer_cache`]), and both are fixed for that whole call. Keys
/// are node ids, valid for the region the call runs in.
#[derive(Default)]
pub(super) struct InferCache {
    types: IdMap<(Key, (u32, u32)), Key>,
    contexts: IdMap<(u32, Key), u32>,
    next: u32,
    /// For each context id, its innermost binder.
    pub(super) info: Vec<CtxBinder>,
    /// Interned windows of binder types, outermost first: (window id of the outer part, the next binder
    /// type inward) to the window's id. 0 is the empty window.
    windows: IdMap<(u32, Key), u32>,
    /// (context id, binders needed) to its window, `None` for a fallback; see [`InferCache::window`].
    window_of: IdMap<(u32, u32), Option<u32>>,
    /// Scratch for [`InferCache::window`]'s walk.
    path: Vec<(u32, u32)>,
    /// [`hc::lowest_loose`]'s memo.
    lows: IdMap<(Key, u32), u32>,
    /// (context id, lowest loose variable, loose range) to [`InferCache::memo_context`]'s answer.
    context_of: IdMap<(u32, u32, u32), (u32, u32)>,
}

thread_local! {
    static INFER_CACHE: std::cell::Cell<InferCache> = std::cell::Cell::default();
}

/// Runs `f` with this thread's [`InferCache`], emptied afterwards ([`InferCache::reset`]). A nested call, or one
/// after a panic, finds the slot empty and starts from a new cache.
fn with_infer_cache<R>(f: impl FnOnce(&mut InferCache) -> R) -> R {
    let mut ic = INFER_CACHE.take();
    let r = f(&mut ic);
    ic.reset();
    INFER_CACHE.set(ic);
    r
}

impl InferCache {
    /// The id of context `cid` extended by a binder of type `a`.
    pub(super) fn enter(&mut self, s: &Spaces, cid: u32, a: &Expr) -> u32 {
        let next = &mut self.next;
        let info = &mut self.info;
        *self.contexts.entry((cid, s.key(a))).or_insert_with(|| {
            *next += 1;
            if info.len() <= *next as usize {
                info.resize(*next as usize + 1, CtxBinder::default());
            }
            // Jump twice as far as the parent when the parent's jump and its jump's jump span equal
            // lengths, else to the parent: every climb then takes O(log run) steps.
            let p = info[cid as usize];
            let (j, jj) = (info[p.jump as usize], info[info[p.jump as usize].jump as usize]);
            let jump = if p.run > 0 && p.run - j.run == j.run - jj.run { j.jump } else { cid };
            info[*next as usize] = CtxBinder { parent: cid, ty: Some(s.key(a)), loose: s.loose(a), run: p.run + 1, jump };
            *next
        })
    }

    /// The context `lo` binders out from `cid`, or `None` when one of those binders has no type of
    /// the term (or is the caller's).
    pub(super) fn skip(&self, cid: u32, lo: u32) -> Option<u32> {
        // Context 0 has no entry until a binder is entered.
        let run = |c: u32| self.info.get(c as usize).map_or(0, |b| b.run);
        let target = run(cid).checked_sub(lo)?;
        let mut c = cid;
        while run(c) > target {
            let b = self.info[c as usize];
            c = if run(b.jump) >= target { b.jump } else { b.parent };
        }
        Some(c)
    }

    /// Empties the cache for the next call, keeping its capacity: a sweep makes thousands of calls, and growing
    /// each one's maps from empty was most of `Checker::infer`'s 0.9% under `reserve_rehash` (`docs/tier-cycle/`,
    /// "Survey: where the growth comes from"). Clearing costs time in the capacity, so a map grown past `KEEP` is let go.
    fn reset(&mut self) {
        const KEEP: usize = 1 << 14;
        fn empty_map<K, V>(m: &mut IdMap<K, V>) {
            if m.capacity() > KEEP {
                *m = IdMap::default();
            } else {
                m.clear();
            }
        }
        fn empty_vec<T>(v: &mut Vec<T>) {
            if v.capacity() > KEEP {
                *v = Vec::new();
            } else {
                v.clear();
            }
        }
        // Every field by name, so a field added later fails to compile here until it is emptied too.
        let InferCache {
            types,
            contexts,
            next,
            info,
            windows,
            window_of,
            path,
            lows,
            context_of,
        } = self;
        empty_map(types);
        empty_map(contexts);
        empty_map(windows);
        empty_map(window_of);
        empty_map(lows);
        empty_map(context_of);
        empty_vec(info);
        empty_vec(path);
        *next = 0;
    }

    /// An id no other context has: for a binder type that isn't a node
    /// of the term, like a `Pair`'s inferred first component.
    pub(super) fn fresh(&mut self) -> u32 {
        self.next += 1;
        if self.info.len() <= self.next as usize {
            self.info.resize(self.next as usize + 1, CtxBinder::default());
        }
        self.info[self.next as usize] = CtxBinder { parent: 0, ty: None, loose: u32::MAX, run: 0, jump: self.next };
        self.next
    }

    /// What `Checker::infer` keys its memo by for node `e` in context `cid`, besides `e`: `(lo, window)`,
    /// the interned window of the binder types `e` can depend on, instead of the whole context.
    /// `lo` is `e`'s lowest loose variable: the `lo` innermost binders are never looked up, so
    /// contexts that differ only there share the entry (a `J` motive's own binders around a shared
    /// term, as in `trans_proof`). Nor is the numbering affected: the answer mentions only binders
    /// from `lo` out, at the same positions. From there, `e`'s loose range
    /// says how many binders it mentions; each of those binders' types may mention outer binders in
    /// turn, so the window grows to cover them (a type with loose range `m` at position `p`, counted
    /// from the innermost, reaches binder `p + m`). Inside that window nothing else is consulted:
    /// `infer` looks up only variables of `e`, and a lookup's answer is that binder's type shifted,
    /// whose own variables are in the window by construction. So two contexts with the same window
    /// give `e` the same answer, in the same variable numbering (indices count from the innermost
    /// binder either way). Window ids have the top bit set, so they never meet a whole-context id (whose
    /// `lo` is 0).
    /// Falls back to `cid` when the window would pass a binder the term doesn't name (`fresh`), or
    /// run past the call's own binders into the caller's context.
    fn memo_context(&mut self, s: &Spaces, cid: u32, e: &Expr) -> (u32, u32) {
        const WINDOW_BIT: u32 = 1 << 31;
        let need = s.loose(e);
        if need == 0 {
            return (0, WINDOW_BIT);
        }
        let lo = hc::lowest_loose(s, e, 0, &mut self.lows);
        if let Some(&r) = self.context_of.get(&(cid, lo, need)) {
            return r;
        }
        // The `lo` innermost binders, which `e` never names, are skipped; skipping a `fresh` binder
        // falls back as passing one inside a window does.
        let r = self.skip(cid, lo).and_then(|c| self.window(c, need - lo)).map_or((0, cid), |w| (lo, WINDOW_BIT | w));
        self.context_of.insert((cid, lo, need), r);
        r
    }

    /// The interned window of the innermost `need` binders of context `cid`, grown over their
    /// types' loose ranges, or `None` for a fallback. The window of `(c, k)` is the window of
    /// `(parent, max(k - 1, loose of c's type))` extended inward by `c`'s binder type, so each
    /// `(c, k)` is computed once (`window_of`) and a lookup costs one probe, however deep the window.
    fn window(&mut self, cid: u32, need: u32) -> Option<u32> {
        let mut path = std::mem::take(&mut self.path);
        path.clear();
        let (mut c, mut k) = (cid, need);
        let mut w = loop {
            if k == 0 {
                break Some(0);
            }
            if let Some(&w) = self.window_of.get(&(c, k)) {
                break w;
            }
            if c == 0 {
                break None;
            }
            let CtxBinder { parent, loose, .. } = self.info[c as usize];
            if loose == u32::MAX {
                break None;
            }
            path.push((c, k));
            (c, k) = (parent, (k - 1).max(loose));
        };
        for &(c, k) in path.iter().rev() {
            if let Some(outer) = w {
                let next = self.windows.len() as u32 + 1;
                let ty = self.info[c as usize].ty.expect("a window binder has a type");
                w = Some(*self.windows.entry((outer, ty)).or_insert(next));
            }
            self.window_of.insert((c, k), w);
        }
        self.path = path;
        w
    }
}

// --- typechecking -----------------------------------------------------

/// The typing context `infer`/`check` thread through every recursive call,
/// growing by one entry per binder entered (`Pi`/`Lam`/`Sigma`/`Pair`) and
/// shrinking back via `truncate` on the way out. A plain `Vec<Expr>` would
/// make each of those binder-entry sites pay an O(current length) clone --
/// negligible for a shallow context, but this kernel's own deeply-recursive
/// callers (`eval_dyn`'s per-instance proof search in particular) can
/// legitimately build up nontrivial context depth, turning that into
/// O(depth^2) total work across one recursive descent. `im::Vector` gives
/// the same by-value, append/truncate-at-the-end API `Ctx`'s callers
/// already use, but backed by structural sharing: `.clone()` and
/// `.push_back()` are both O(log n) (amortized ~O(1) in practice) instead
/// of O(n), so this cost disappears without changing any call site's own
/// control flow.
pub type Ctx = im::Vector<Expr>;

/// The global environment: constant `l`'s type is `globals[l]`, closed, so
/// no binder or later global changes what it means. Kept apart from
/// [`Ctx`], the kernel's own binders, so a `Const` can never resolve to
/// one: with a single vector, `(λx:A. Const(L)) a` would reduce to a
/// `Const(L)` that no longer refers to anything.
///
/// Trusted like `Ctx`: nothing checks that an entry is a type, and a
/// constant is an axiom.
pub type Globals = im::Vector<PExpr>;

/// The checker's working context: the caller's `base` plus the binders
/// entered since, in a plain `Vec` pushed and truncated in place. Cloning
/// and pushing an `im::Vector` at every binder copies a shared tail
/// (about 15% of samples on the bit-vector lemma); `base` is cloned once
/// per top-level call.
struct CtxScope {
    base: Ctx,
    local: Vec<Expr>,
}

impl CtxScope {
    fn new(base: &Ctx) -> CtxScope {
        CtxScope { base: base.clone(), local: Vec::new() }
    }
}

fn ctx_lookup(s: &Spaces, ctx: &CtxScope, k: u32) -> Result<Expr, String> {
    let k_usize = k as usize;
    let len = ctx.base.len() + ctx.local.len();
    if k_usize >= len {
        return Err(format!("unbound variable #{k}"));
    }
    let idx = len - 1 - k_usize;
    let ty = if idx < ctx.base.len() { &ctx.base[idx] } else { &ctx.local[idx - ctx.base.len()] };
    if s.free(ty) > 0 {
        return Err(free_escaped(s.free(ty) - 1));
    }
    // `ctx[idx]` was checked when the context had length `idx` (that many
    // entries existed before it was pushed); reinterpreting it at the
    // current length requires shifting by `k + 1`, not `k` — e.g. for
    // `Var(0)` itself (k=0), its stored type was written one binder
    // shallower than "now", so it still needs a shift of 1.
    Ok(shift_in(s, ty, 0, k as i32 + 1))
}

/// Constant `l`'s type: `globals[l]` as is, since a closed type has no
/// variable to shift. An error when `l` is past the environment, or when
/// the type isn't closed.
fn const_type(s: &Spaces, g: &Globals, l: u32) -> Result<Expr, String> {
    match g.get(l as usize).map(PExpr::get) {
        Some(ty) if s.loose(&ty) == 0 && s.free(&ty) == 0 => Ok(ty),
        Some(ty) => Err(format!("constant @{l}'s type isn't closed: {}", brief(&ty))),
        None => Err(format!("unknown constant @{l}")),
    }
}


pub(super) fn expect_sort(s: &Spaces, e: &Expr) -> Result<u32, String> {
    let w = whnf_in(s, e);
    match s.node(&w) {
        Node::Sort(i) => Ok(i),
        _ => Err(format!("expected a Sort, got {}", brief(&w))),
    }
}

fn expect_pi(s: &Spaces, e: &Expr) -> Result<(Expr, Expr), String> {
    let w = whnf_in(s, e);
    match s.node(&w) {
        Node::Pi(a, b) => Ok((a, b)),
        _ => Err(format!("expected a Pi type, got {}", brief(&w))),
    }
}

fn expect_w(s: &Spaces, e: &Expr) -> Result<(Expr, Expr), String> {
    let w = whnf_in(s, e);
    match s.node(&w) {
        Node::W(a, b) => Ok((a, b)),
        _ => Err(format!("expected a W type, got {}", brief(&w))),
    }
}

fn expect_sigma(s: &Spaces, e: &Expr) -> Result<(Expr, Expr), String> {
    let w = whnf_in(s, e);
    match s.node(&w) {
        Node::Sigma(a, b) => Ok((a, b)),
        _ => Err(format!("expected a Sigma type, got {}", brief(&w))),
    }
}

/// One type check in progress: the spaces and globals it reads, the inference memo, and the context entered so far with
/// its id (`InferCache::enter`).
struct Checker<'c> {
    s: &'c Spaces,
    g: &'c Globals,
    ic: &'c mut InferCache,
    ctx: CtxScope,
    cid: u32,
}

impl Checker<'_> {
    /// Runs `f` under one more binder, of type `a` and context id `cid`, restoring the context afterwards (on error too).
    fn under<R>(&mut self, a: Expr, cid: u32, f: impl FnOnce(&mut Self) -> R) -> R {
        let (depth, outer) = (self.ctx.local.len(), self.cid);
        self.ctx.local.push(a);
        self.cid = cid;
        let r = f(self);
        self.ctx.local.truncate(depth);
        self.cid = outer;
        r
    }

    /// `infer`'s own `Sigma`/`Pair`/`SigRec` cases, out of line, so these
    /// arms' locals don't sit in `infer`'s frame on every *other* shape.
    ///
    /// This, and every other `#[inline(never)]` extraction in this module,
    /// was once load-bearing: `eval_dyn`'s per-instance proof search ran
    /// close to a native-stack budget tuned in a debug test thread, and
    /// inlining these arms back into `infer` measurably shrank its margin
    /// and overflowed a deep-recursion test. Every traversal here, and
    /// `eval_dyn`, now runs through [`grow`] (`docs/related-work/` 31, 32), so
    /// frame size only decides how soon a deep walk moves to a new stack
    /// segment. They are kept because smaller hot frames cost nothing, not
    /// because anything depends on them.
    #[inline(never)]
    fn infer_sigma(&mut self, a: &Expr, b: &Expr) -> Result<Expr, String> {
        let s = self.s;
        let i = expect_sort(s, &self.infer(a)?)?;
        let cid2 = self.ic.enter(s, self.cid, a);
        let j = self.under(*a, cid2, |c| c.infer(b));
        let j = expect_sort(s, &j?)?;
        Ok(sort(i.max(j)))
    }

    #[inline(never)]
    fn infer_pair(&mut self, fam: &Expr, a: &Expr, b: &Expr) -> Result<Expr, String> {
        let s = self.s;
        let ta = self.infer(a)?;
        let cid2 = self.ic.fresh();
        let tf = self.under(ta, cid2, |c| c.infer(fam));
        expect_sort(s, &tf?)?;
        let expected_b_ty = subst_top(s, fam, a);
        self.check(b, &expected_b_ty)?;
        Ok(sigma(ta, *fam))
    }

    #[inline(never)]
    fn infer_sigrec(&mut self, motive: &Expr, step: &Expr, target: &Expr) -> Result<Expr, String> {
        let s = self.s;
        let (sa, sb) = expect_sigma(s, &self.infer(target)?)?;
        self.infer(motive)?; // sanity: motive must itself be well-typed

        // step : Pi a:A. Pi b:B(a). motive (pair(B,a,b))
        // `sb` already assumes exactly one binder (`Sigma`'s own convention)
        // -- b's own domain under binder `a` (depth1) is `sb` unchanged, the
        // same way `WRec`'s own `f_dom_d1` reuses `wb` unchanged.
        let b_dom_d1 = sb;
        // under binders a(Var1), b(Var0) -- depth2:
        let motive_d2 = shift_in(s, motive, 0, 2);
        // `sb`'s own bound tag (Var0) must stay untouched (`Pair`'s own `fam`
        // field needs a *fresh* tag binder of its own, one level below
        // wherever the `Pair` itself sits) -- only whatever `sb` references
        // *above* that (the 2 extra binders `a`/`b` now sitting between it
        // and the ambient context) shifts, cutoff 1.
        let fam_d2 = shift_in(s, &sb, 1, 2);
        let concl_d2 = app(motive_d2, pair(fam_d2, var(1), var(0)));
        let expected_step_ty = pi(sa, pi(b_dom_d1, concl_d2));
        self.check(step, &expected_step_ty)?;

        Ok(app(*motive, *target))
    }

    /// `infer`'s own `Sup` arm, out of line: `ta`/`dom`/`cod`/`w_candidate`/
    /// `wa`/`wb` would otherwise sit in `infer`'s frame on every call (see
    /// `infer_sigma`).
    #[inline(never)]
    fn infer_sup(&mut self, a: &Expr, f: &Expr) -> Result<Expr, String> {
        let s = self.s;
        let ta = self.infer(a)?;
        let (dom, cod) = expect_pi(s, &self.infer(f)?)?;
        // `cod` is written one binder deeper than `f`'s own domain binder; a
        // `Sup`'s codomain must not actually depend on it -- enforced here
        // (not just documented), by an occurs-check on `cod`'s own normal
        // form, since `subst_top` just below would otherwise only ever be
        // validated at this one concrete `a`, silently trusting every other
        // point of `f`'s domain agrees.
        let cod_nf = nf_in(s, &cod);
        if is_var_free(s, &cod_nf, 0) {
            return Err(sup_codomain_depends_on_own_argument(&cod_nf));
        }
        let w_candidate = subst_top(s, &cod, a);
        let (wa, wb) = expect_w(s, &w_candidate)?;
        if !def_eq_in(s, &wa, &ta) {
            return Err(format!("sup: element type mismatch: {} vs {}", brief(&wa), brief(&ta)));
        }
        let expected_dom = subst_top(s, &wb, a);
        if !def_eq_in(s, &dom, &expected_dom) {
            return Err(format!(
                "sup: children-function domain mismatch: {} vs {}",
                brief(&dom),
                brief(&expected_dom)
            ));
        }
        Ok(wty(wa, wb))
    }

    /// `infer` on a child. A node with two or more parents is memoised by
    /// node and context id, so a shared subterm is inferred once per context
    /// rather than once per occurrence (`docs/related-work/` §63). A node with one
    /// parent can only be reached twice through a shared ancestor, which is
    /// memoised instead, so skipping it keeps the walk linear in the DAG and
    /// costs unshared terms no hashing. Only successes are stored: an error
    /// ends the whole check.
    fn infer(&mut self, e: &Expr) -> Result<Expr, String> {
        let s = self.s;
        if !s.shared(e) {
            return self.infer_node(e);
        }
        // Keyed by the window of binders the node can depend on, not the whole context, so one
        // inference serves every binder stack that agrees on that window (bit-vector design doc §50:
        // 96 to 99.5% of the whole-context misses were such repeats).
        let key = (s.key(e), self.ic.memo_context(s, self.cid, e));
        if let Some(ty) = self.ic.types.get(&key) {
            return Ok(s.expr_of(ty));
        }
        let ty = self.infer_node(e)?;
        self.ic.types.insert(key, s.key(&ty));
        Ok(ty)
    }

    fn infer_node(&mut self, e: &Expr) -> Result<Expr, String> {
        let s = self.s;
        s.tick();
        grow(|| match s.node(e) {
            Node::Var(k) => ctx_lookup(s, &self.ctx, k),
            Node::Sort(i) => i.checked_add(1).map(sort).ok_or_else(|| format!("universe overflow: no successor sort above Type{i}")),
            Node::Const(l) => const_type(s, self.g, l),
            Node::Free(l) => Err(free_escaped(l)),
            Node::Pi(a, b) => {
                let i = expect_sort(s, &self.infer(&a)?)?;
                let cid2 = self.ic.enter(s, self.cid, &a);
                let j = self.under(a, cid2, |c| c.infer(&b));
                let j = expect_sort(s, &j?)?;
                Ok(sort(i.max(j)))
            }
            Node::Lam(a, body) => {
                expect_sort(s, &self.infer(&a)?)?;
                let cid2 = self.ic.enter(s, self.cid, &a);
                let tbody = self.under(a, cid2, |c| c.infer(&body));
                let tbody = tbody?;
                Ok(pi(a, tbody))
            }
            Node::App(..) => {
                // The whole spine `h a1 ... ak` at once, as `beta_spine` does for reduction: each domain
                // is instantiated with the arguments before it and the last codomain once with all of
                // them, instead of one `subst_top` per argument, each copying the rest of the telescope.
                // A codomain that is not syntactically a Pi takes the pending arguments first, then whnf.
                let mut args = vec![];
                let mut head = *e;
                while let Node::App(f, a) = s.node(&head) {
                    args.push(a);
                    head = f;
                }
                args.reverse();
                let mut ty = self.infer(&head)?;
                let mut pending: Vec<&Expr> = vec![];
                for a in &args {
                    if !matches!(s.node(&ty), Node::Pi(..)) && !pending.is_empty() {
                        ty = instantiate_n(s, &ty, &pending, 0);
                        pending.clear();
                    }
                    let (dom, cod) = expect_pi(s, &ty)?;
                    let dom = if pending.is_empty() { dom } else { instantiate_n(s, &dom, &pending, 0) };
                    self.check(a, &dom)?;
                    pending.push(a);
                    ty = cod;
                }
                Ok(instantiate_n(s, &ty, &pending, 0))
            }
            Node::Id(a, x, y) => {
                let i = expect_sort(s, &self.infer(&a)?)?;
                self.check(&x, &a)?;
                self.check(&y, &a)?;
                Ok(sort(i))
            }
            Node::Refl(a) => {
                let ta = self.infer(&a)?;
                Ok(id(ta, a, a))
            }
            Node::J { motive, base, a, b, p } => {
                let ta = self.infer(&a)?;
                self.check(&b, &ta)?;
                self.check(&p, &id(ta, a, b))?;
                self.infer(&motive)?; // sanity: motive must itself be well-typed
                let expected_base_ty = pi(ta, app3(shift_in(s, &motive, 0, 1), var(0), var(0), refl(var(0))));
                self.check(&base, &expected_base_ty)?;
                Ok(app3(motive, a, b, p))
            }
            Node::W(a, b) => {
                let i = expect_sort(s, &self.infer(&a)?)?;
                let cid2 = self.ic.enter(s, self.cid, &a);
                let j = self.under(a, cid2, |c| c.infer(&b));
                let j = expect_sort(s, &j?)?;
                Ok(sort(i.max(j)))
            }
            Node::Sup(a, f) => self.infer_sup(&a, &f),
            Node::WRec { motive, children_ty, step, target } => {
                let (wa, wb) = expect_w(s, &self.infer(&target)?)?;
                // Soundness gate for `whnf_in`'s own use of `children_ty`
                // (see `Node::WRec`'s own doc): `target`'s *real* children-type
                // family, independently re-derived here from its own inferred
                // type, must match the field a `WRec` term carries exactly --
                // otherwise a term built with a wrong `children_ty` would
                // reduce its own induction-hypothesis closure to a domain that
                // lies about what's actually being recursed into, letting an
                // otherwise-untyped step function's body get away with
                // anything at that domain.
                if !def_eq_in(s, &children_ty, &wb) {
                    return Err(wrec_children_ty_mismatch(&children_ty, &wb));
                }
                self.infer(&motive)?;
                let w_ty0 = wty(wa, wb);

                // f : B(a) -> W(A,B), formed under binder `a` (depth 1).
                let f_dom_d1 = wb; // wb already assumes exactly one binder
                let f_ty_d1 = pi(f_dom_d1, shift_in(s, &w_ty0, 0, 2));

                // under binders a (Var1), f (Var0) — depth 2:
                // ih_ty : Pi y : B(a). motive (f y)      [formed at depth2, body at depth3]
                let ih_dom_d2 = shift_in(s, &wb, 0, 1); // B(a) reindexed for depth-2 frame
                let motive_d3 = shift_in(s, &motive, 0, 3);
                let f_at_d3 = var(1); // f, seen from depth3 (a=2,f=1,y=0)
                let y_at_d3 = var(0);
                let ih_body_d3 = app(motive_d3, app(f_at_d3, y_at_d3));
                let ih_ty_d2 = pi(ih_dom_d2, ih_body_d3);

                // concl_ty : motive (sup a f), at depth2 (a=1, f=0)
                let motive_d2 = shift_in(s, &motive, 0, 2);
                let concl_ty_d2 = app(motive_d2, sup(var(1), var(0)));

                let arrow_ty_d2 = pi(ih_ty_d2, shift_in(s, &concl_ty_d2, 0, 1));

                let expected_step_ty = pi(wa, pi(f_ty_d1, arrow_ty_d2));
                self.check(&step, &expected_step_ty)?;

                Ok(app(motive, target))
            }
            Node::Sigma(a, b) => self.infer_sigma(&a, &b),
            Node::Pair(fam, a, b) => self.infer_pair(&fam, &a, &b),
            Node::SigRec { motive, step, target } => self.infer_sigrec(&motive, &step, &target),
        })
    }

    fn check(&mut self, e: &Expr, expected: &Expr) -> Result<(), String> {
        let s = self.s;
        grow(|| {
            if let Node::Lam(a, body) = s.node(e)
                && let Node::Pi(dom, cod) = s.node(&whnf_in(s, expected))
            {
                // As `infer`'s `Lam` rule does: `def_eq` alone would accept an
                // ill-typed annotation that reduces to `dom`.
                expect_sort(s, &self.infer(&a)?)?;
                if !def_eq_in(s, &a, &dom) {
                    return Err(format!("lambda domain mismatch: {} vs {}", brief(&a), brief(&dom)));
                }
                let cid2 = self.ic.enter(s, self.cid, &a);
                return self.under(a, cid2, |c| c.check(&body, &cod));
            }
            let inferred = self.infer(e)?;
            if def_eq_in(s, &inferred, expected) {
                Ok(())
            } else {
                Err(format!(
                    "type mismatch: inferred {}, expected {}",
                    brief_nf(&inferred),
                    brief_nf(expected)
                ))
            }
        })
    }
}




/// `infer`'s own `WRec` mismatch error, out of line and `#[cold]` so its
/// own locals (two `nf` calls, a `format!`) stay off `infer`'s hot frame
/// (see `infer_sigma`).
#[cold]
#[inline(never)]
fn wrec_children_ty_mismatch(children_ty: &Expr, wb: &Expr) -> String {
    format!("wrec: children_ty doesn't match target's own real children-type: {} vs {}", brief_nf(children_ty), brief_nf(wb))
}


/// `e`'s type, with constants typed by `globals` and variables by `ctx`.
/// A `Free` anywhere in `e` is an error; so is one in a `ctx` entry, when
/// `e` uses it.
///
/// Checked here, not only at the leaf: `infer` hands some children to
/// `Checker::check` (an `App`'s argument, `Id`'s sides, `J`'s fields), whose
/// `Lam` rule against a `Pi` compares the domain by `def_eq` and never
/// infers it, and `WRec`'s `children_ty` is only compared, so a `Free`
/// under a redex in any of them would reduce away unseen. `free` is
/// O(1).
pub fn infer_in(globals: &Globals, ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    if e.free() > 0 {
        return Err(free_escaped(e.free() - 1));
    }
    scoped(|| with_spaces(|s| with_infer_cache(|ic| Checker { s, g: globals, ic, ctx: CtxScope::new(ctx), cid: 0 }.infer_node(e))))
}

/// [`infer_in`] with no globals.
pub fn infer(ctx: &Ctx, e: &Expr) -> Result<Expr, String> {
    infer_in(&Globals::new(), ctx, e)
}



/// Checks `e` against `expected`.
///
/// Safe at any depth: every traversal it reaches runs through [`grow`],
/// so an expression is bounded by heap, not native stack. That is also
/// why there is no depth guard here or in [`typecheck`] any more -- the
/// one that used to exist (`MAX_CHECK_DEPTH`, `docs/related-work/` 30) was
/// purely a stack-survival bound. How long a deep check takes is the
/// caller's to bound; `proof.rs`'s step budgets do that.
pub fn check_in(globals: &Globals, ctx: &Ctx, e: &Expr, expected: &Expr) -> Result<(), String> {
    // Checked here, not only at the leaf: `check`'s `Lam` rule never
    // infers the lambda's domain, `WRec`'s `children_ty` is only compared,
    // and nothing infers `expected`, so a `Free` under a redex in any of
    // them would reduce away unseen. `free` is O(1).
    for t in [e, expected] {
        if t.free() > 0 {
            return Err(free_escaped(t.free() - 1));
        }
    }
    // The claim must be a type before anything is checked against it, as
    // in Lean's `check_constant_val` and Coq's `infer_definition`
    // (docs/related-work/ §67): the rules below compare `expected` by `def_eq`
    // and never infer it, so a malformed claim would otherwise be proved.
    // One cache for both, so a claim's subterms the proof shares hit it.
    scoped(|| {
        with_spaces(|s| {
            let large = hc::large(s, e, expected);
            let body = || {
                with_infer_cache(|ic| {
                    let mut c = Checker { s, g: globals, ic, ctx: CtxScope::new(ctx), cid: 0 };
                    expect_sort(s, &c.infer(expected)?)?;
                    c.check(e, expected)
                })
            };
            if large && !room(CHECK_SEGMENT) { on_segment(CHECK_SEGMENT, body) } else { body() }
        })
    })
}

/// [`check_in`] with no globals.
pub fn check(ctx: &Ctx, e: &Expr, expected: &Expr) -> Result<(), String> {
    check_in(&Globals::new(), ctx, e, expected)
}

/// (distinct nodes, nodes counted once per occurrence) in `e`.
pub fn term_sizes(e: &Expr) -> (usize, u128) {
    fn go(e: &Expr, seen: &mut HashMap<u64, u128>) -> u128 {
        let mut n = 1u128;
        e.node().for_kids(|p, _| {
            let k = node_key(p);
            n += match seen.get(&k) {
                Some(&t) => t,
                None => {
                    let t = grow(|| go(p, seen));
                    seen.insert(k, t);
                    t
                }
            };
        });
        n
    }
    let mut seen = HashMap::new();
    let tree = go(e, &mut seen);
    (seen.len() + 1, tree)
}


/// Typecheck a closed term and return its normalized type.
pub fn typecheck(e: &Expr) -> Result<Expr, String> {
    scoped(|| infer(&Ctx::new(), e).map(|t| with_spaces(|s| nf_in(s, &t))))
}

