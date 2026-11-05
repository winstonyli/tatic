use super::*;

/// The join's searches run (`join_search`), the terms they reached, how many met, the memo hits that ran none, and the
/// time in the searches, of it in those that failed; the joins `JoinStore` served, and the time in its queries (served
/// or not).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct JoinCost {
    pub searches: u64,
    pub reached: u64,
    pub met: u64,
    pub hits: u64,
    pub nanos: u64,
    pub failed_nanos: u64,
    pub stored: u64,
    pub store_nanos: u64,
}

impl JoinCost {
    /// the counts from `before` to `self` (a job's `join_cost` at two times)
    pub fn since(self, before: JoinCost) -> JoinCost {
        self.zip(before, |a, b| a - b)
    }

    /// `other`'s counts added to these
    pub fn add(&mut self, other: JoinCost) {
        *self = self.zip(other, |a, b| a + b);
    }

    fn zip(self, o: JoinCost, f: impl Fn(u64, u64) -> u64) -> JoinCost {
        JoinCost {
            searches: f(self.searches, o.searches),
            reached: f(self.reached, o.reached),
            met: f(self.met, o.met),
            hits: f(self.hits, o.hits),
            nanos: f(self.nanos, o.nanos),
            failed_nanos: f(self.failed_nanos, o.failed_nanos),
            stored: f(self.stored, o.stored),
            store_nanos: f(self.store_nanos, o.store_nanos),
        }
    }
}

/// A join step `JoinStore` keeps: the step at `path` from `from` by the law `lhs = rhs` read in direction `backward`, which
/// a table holds under that key (`RuleTable::join_key`) whatever its index.
#[derive(Clone, Copy)]
struct StoredStep {
    from: Term,
    path: StepPath,
    law: (Term, Term, bool),
}

/// The steps of the join's met paths, as edges between the terms they join: each term's neighbours, by the step and
/// whether it is walked backwards. A path through steps whose laws the current table holds proves its ends equal, so
/// `join_eq` serves a pair from the store before it searches. The miner keeps one per mine, fed by its main thread's
/// searches with the memo on (not its proofs, which run on that thread only at some thread counts); its workers read a
/// copy frozen when a round of scoring starts, so a candidate's gain depends neither on the thread count nor on which
/// worker scored what (docs/tier-cycle.md, "Spike of the join store"). The copy is the whole store, once a round.
#[derive(Clone, Default)]
pub struct JoinStore {
    edges: hashbrown::HashMap<Term, Vec<StoredEdge>>,
}

/// An edge of `JoinStore` from the term it is kept under: to `to` by `step`, walked backwards (from `step`'s result to
/// `step.from`) if `back`.
#[derive(Clone, Copy)]
struct StoredEdge {
    to: Term,
    step: StoredStep,
    back: bool,
}

/// How a thread uses a join store: feeding it from its met searches and reading it, or reading a frozen copy.
pub enum JoinStoreUse {
    Feed(JoinStore),
    Read(std::sync::Arc<JoinStore>),
}

impl JoinStoreUse {
    /// A frozen copy of the store this use feeds, for the jobs that read it; `None` for a reader.
    pub fn frozen(&self) -> Option<std::sync::Arc<JoinStore>> {
        match self {
            JoinStoreUse::Feed(store) => Some(std::sync::Arc::new(store.clone())),
            JoinStoreUse::Read(_) => None,
        }
    }

    fn store(&self) -> &JoinStore {
        match self {
            JoinStoreUse::Feed(store) => store,
            JoinStoreUse::Read(store) => store,
        }
    }
}

impl JoinStore {
    fn add(&mut self, to: Term, step: StoredStep) {
        let v = self.edges.entry(step.from).or_default();
        if !v.iter().any(|e| e.to == to && e.step.law == step.law && e.step.path == step.path) {
            v.push(StoredEdge { to, step, back: false });
            self.edges.entry(to).or_default().push(StoredEdge { to: step.from, step, back: true });
        }
    }
    /// The plan of `a = b` along the shortest stored path through the job's laws and terms of at most `cap` nodes, looked
    /// for among `join_visit()` terms at most, as the search, and the path's terms.
    fn path(&self, job: &Job, a: Term, b: Term, cap: usize) -> Option<(PlanRc, Vec<Term>)> {
        let table = &*job.rules().table;
        let mut prev: hashbrown::HashMap<Term, Option<(Term, StoredStep, bool, u32)>> = [(a, None)].into_iter().collect();
        let (mut front, visit) = (vec![a], join_visit(job));
        // bounded by the terms reached, as the search is (here checked once a layer)
        while !front.is_empty() && prev.len() <= visit {
            for t in std::mem::take(&mut front) {
                for &StoredEdge { to: u, step, back } in self.edges.get(&t).into_iter().flatten() {
                    let Some(&eq) = table.join_key.get(&step.law) else { continue };
                    if u.size() > cap || prev.contains_key(&u) {
                        continue;
                    }
                    prev.insert(u, Some((t, step, back, eq)));
                    if u == b {
                        // back from `b`: each step's plan, `p = x` read forwards
                        let (mut plans, mut terms, mut x) = (vec![], vec![b], b);
                        while let Some((p, step, back, eq)) = prev[&x] {
                            let plan = step_plan(job, &JoinStep { from: step.from, path: step.path, eq });
                            plans.push(if back { Plan::sym(job, plan) } else { plan });
                            terms.push(p);
                            x = p;
                        }
                        return Some((plans.into_iter().rev().reduce(|a, b| Plan::trans(job, a, b)).expect("a step"), terms));
                    }
                    front.push(u);
                }
            }
        }
        None
    }
}

/// The plan of `a = b` from the job's join store under the current table, and the path's terms.
pub(super) fn stored_join(job: &Job, a: Term, b: Term) -> Option<(PlanRc, Vec<Term>)> {
    let cap = a.size().max(b.size()) + 2;
    job.join_store.as_ref()?.store().path(job, a, b, cap)
}

/// `t` with every occurrence of the subterm `x` replaced by `with`.
pub fn replace_term(t: &Term, x: &Term, with: &Term) -> Term {
    if t == x {
        return *with;
    }
    match *t.node() {
        Node::Op(o, a, b) => Term::op(o, replace_term(&a, x, with), replace_term(&b, x, with)),
        _ => *t,
    }
}

/// The plan of `a = b` (over `k` variables) for rewritten terms: `refl`; the bitwise law over atoms (when it holds on all
/// bit values, so the kernel check cannot fail); the per-position law; the class table's normal forms (when both sides
/// meet); the bit-0 mask reduction; or the whole-term machine
/// proof. `None` otherwise.
pub fn prove_eq(job: &mut Job, n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    if a == b {
        return Some(Plan::refl(job, a));
    }
    // each step below can be switched off: `ABLATE=eq_truth,eq_pos,shrmask`
    let mut atoms = vec![];
    if let (false, Some(a1), Some(a2)) = (job.setup().ablated("eq_truth"), abstract_atoms(a, &mut atoms, k), abstract_atoms(b, &mut atoms, k)) {
        let holds = (0..1usize << k).all(|m| {
            let bits: Vec<bool> = (0..k).map(|v| m >> v & 1 == 1).collect();
            term_gb(&Bools, &a1, &bits) == term_gb(&Bools, &a2, &bits)
        });
        if holds {
            let args = (0..k).map(|i| atoms.get(i).cloned().unwrap_or(Term::v(0))).collect();
            return Some(Plan::law(job, LawKind::Bitwise, a1, a2, args));
        }
    }
    // add-free terms with shifts: the per-position prover, when the law holds exhaustively at widths 1..=5 (a position
    // reads only a few neighbours, so widths this small contain every case; the kernel checks the proof regardless)
    if !job.setup().ablated("eq_pos") && k <= 3 && a.add_free() && b.add_free() && (a.has_shift() || b.has_shift()) && bitwise_holds(a, b, k) {
        return Some(Plan::law(job, LawKind::Bitwise, *a, *b, vars(k)));
    }
    // the class table's normal form of both sides was a step here (spec 2026-10-22-class-table-normal-form-design.md
    // §4); with the table's step in the rewriter, the sides arrive normalized, so it closed nothing and was deleted
    // (docs/tier-cycle.md, "Ablations of the class table")
    // congruence on equal operators and generalizing a shared subterm into a variable were removed: neither decided a law
    // (docs/tier-cycle.md, "Ablating the fixed rewriter and prover parts")
    if let Some(p) = shr_mask_eq(job, n, k, a, b) {
        return Some(p);
    }
    join_or_machine(job, n, k, a, b)
}

/// The whole-term machine proof of `a = b` (the carry-encoding proof for the two terms as bit-serial machines), counted in
/// `RewriteState::fallbacks`; `None` when there is none.
fn machine_fallback(job: &mut Job, n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    let cost = |t: &Term| Machine::parse(t).map_or(0, |m| m.carries());
    // scoring mode: only whether the rewriting needed this fallback matters, so count it without searching for the encoding (the
    // plan may then not compile); a pair that is not equal fails here as it would in `tree_encoding` (else congruence on unequal
    // operands would count two proofs); a few tuples suffice to tell, since unequal pairs differ almost everywhere
    let screened = job.rules().score_only && Machine::parse(a).is_some() && Machine::parse(b).is_some() && cost(a).max(cost(b)) <= carry_cap(job);
    if screened && a.differs_in(b, n, k, 16) || !screened && tree_encoding(job, n, k, a, b).is_none() {
        return None;
    }
    job.rw.fallbacks += 1;
    Some(Plan::law(job, LawKind::Tree, *a, *b, vars(k)))
}

/// `a = b` by the bounded join, else by the whole-term machine proof: the floor laws' normal forms all join within a few
/// equation steps (docs/tier-cycle.md, "Equational reach of the floor").
pub(super) fn join_or_machine(job: &mut Job, n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    join_eq(job, n, k, a, b).or_else(|| machine_fallback(job, n, k, a, b))
}

/// One step the join may take: `from -> to` over the pattern variables `V(0..vars)`, an instance of the proved law
/// `lhs = rhs` of `kind` (read right to left when `backward`).
#[derive(Clone, Copy)]
pub(super) struct JoinEq {
    pub(super) from: Term,
    pub(super) to: Term,
    vars: usize,
    pub(super) kind: LawKind,
    pub(super) lhs: Term,
    pub(super) rhs: Term,
    pub(super) backward: bool,
    pub(super) need: Need,
}

/// How many nodes a join step needs, found without matching, so `join_walk` skips a step over the cap unmatched. When every
/// variable occurs in `to` at least as often as in `from`, the step at `t` has `size(t) + size(to) - size(from)` nodes or
/// more (each binding is counted in `to` at least as often as in `t`): it needs that growth from the room the cap leaves
/// above `size(t)`. Otherwise each variable binds at least one node, so it needs `size(to)` of the cap (`of_cap`). 43% of
/// the join's matcher calls have a bound over the cap (docs/tier-cycle.md, "How much the size bound would skip").
#[derive(Clone, Copy, Debug)]
pub(super) struct Need {
    nodes: isize,
    of_cap: bool,
}

impl Need {
    pub(super) fn skips(self, room: isize, cap: isize) -> bool {
        self.nodes > if self.of_cap { cap } else { room }
    }
}

impl JoinEq {
    fn new(from: Term, to: Term, vars: usize, kind: LawKind, lhs: Term, rhs: Term, backward: bool) -> JoinEq {
        let (mut of, mut ot) = ([0; RULE_VARS], [0; RULE_VARS]);
        (from.occurrences(&mut of), to.occurrences(&mut ot));
        let need = match of.iter().zip(&ot).all(|(f, t)| t >= f) {
            true => Need { nodes: to.size() as isize - from.size() as isize, of_cap: false },
            false => Need { nodes: to.size() as isize, of_cap: true },
        };
        JoinEq { from, to, vars, kind, lhs, rhs, backward, need }
    }
}

/// Whether `from -> to` can be a join step: `from` is not a bare variable, binds every variable of `to`, and keeps `lt` at the
/// root (`lt` occurs nowhere else).
pub(super) fn join_usable(from: &Term, to: &Term) -> bool {
    let is_lt = |t: &Term| matches!(*t.node(), Node::Op(LT, ..));
    !matches!(*from.node(), Node::V(_)) && (0..RULE_VARS).all(|v| !to.has_var(v) || from.has_var(v)) && is_lt(from) == is_lt(to)
}

/// The join's steps: every rule not ablated (built-in, promoted and mined), add's associativity and commutativity and those of
/// and, or and xor, each rule and associativity both ways where `join_usable`.
pub(super) fn join_eqs(setup: &Setup, rules: &[TableRule]) -> Vec<JoinEq> {
    let (x, y, z) = (Term::v(0), Term::v(1), Term::v(2));
    let op = Term::op;
    let mut laws: Vec<(LawKind, Term, Term, bool)> = rules.iter().filter(|r| !setup.ablated(r.name)).map(|r| (LawKind::Rule(r.name), r.lhs, r.rhs, true)).collect();
    laws.push((LawKind::Assoc, op(ADD, op(ADD, x, y), z), op(ADD, x, op(ADD, y, z)), true));
    laws.push((LawKind::Comm, op(ADD, x, y), op(ADD, y, x), false));
    for o in [AND, OR, XOR] {
        laws.push((LawKind::Bitwise, op(o, op(o, x, y), z), op(o, x, op(o, y, z)), true));
        laws.push((LawKind::Bitwise, op(o, x, y), op(o, y, x), false));
    }
    let mut eqs = vec![];
    for (kind, lhs, rhs, both) in laws {
        let vars = lhs.max_var().max(rhs.max_var()) + 1;
        for (from, to, backward) in [(lhs, rhs, false), (rhs, lhs, true)] {
            if (both || !backward) && join_usable(&from, &to) {
                eqs.push(JoinEq::new(from, to, vars, kind, lhs, rhs, backward));
            }
        }
    }
    eqs
}

/// How many terms the join reaches at most, `JOIN_VISIT` (1000): its searches and `JoinStore`'s queries.
fn join_visit(job: &Job) -> usize {
    job.setup().or("JOIN_VISIT", 1000)
}

/// The plan of `a = b` by joining them: from both at once over `join_eqs`, the side with fewer pending terms expanding its
/// one with the least depth plus size (a step that grows the term by a node costs 2, a same-size one 1, one that shrinks
/// it by a node 0; against breadth-first, a lower stream M for about a third less CPU: docs/tier-cycle.md, "Depth plus
/// size on the sweep"), through terms of at most the larger side's size plus 2 nodes, until the two reached sets meet or
/// more than `JOIN_VISIT` (1000) terms are reached (5000 left a few laws fewer to the machine proof for 2-3 times the sweep time:
/// docs/tier-cycle.md, "The bounded join removes the floor"). Only pairs equal on random inputs are searched, so an unequal
/// pair costs no search. `ABLATE=join` switches it off. With the memo on, a pair the job's `JoinStore` has a path for
/// is served from it without a search (77% of a cold:cmp3d mine's searches: docs/tier-cycle.md, "Spike of the join store").
/// The terms it examined go to `RewriteState::trace` (`Fired::Join`) and, with the result, to `RewriteState::memo`'s `joins`, so the rule
/// miner reuses it as it does a rewrite: a failed search, all of them (under other rules it is the same search when no rule
/// in or out touches them), served only while the store has no path for the pair; a met one, the terms on its path and their subterms, where the rules its plan used fired (the
/// plan stays a proof while no rule it used is removed, so rules added elsewhere keep it). That is inexact where added rules
/// would push the search over `JOIN_VISIT` before it meets: the
/// cap makes the join non-monotone in its rules, and no rule-independent cap tried was as strong at the same cost
/// (docs/decisions/2026-10-17-monotone-join.md).
pub fn join_eq(job: &mut Job, n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    if job.setup().ablated("join") || a.differs_in(b, n, k, 16) {
        return None;
    }
    // the memo holds searches with no rule blocked (`Job::blocked`), and a plan made while counting serves only a caller that counts
    let memo_on = job.rw.memo.as_ref().is_some_and(|m| m.k == k) && job.blocked.is_empty();
    let traced = job.rw.trace.is_some();
    let counting = job.rules().score_only;
    let key = (*a, *b);
    let replay = |job: &mut Job, trace: &Trace| {
        if let Some(v) = job.rw.trace.as_mut() {
            v.extend_from_slice(trace.items());
        }
    };
    let stored = |job: &mut Job| {
        let t0 = std::time::Instant::now();
        let s = stored_join(job, *a, *b);
        job.join_cost.store_nanos += t0.elapsed().as_nanos() as u64;
        s
    };
    let mut from_store = None;
    if memo_on {
        let hit = job.rw.memo.as_ref().and_then(|m| m.joins.get(&key).cloned());
        if let Some(e) = hit.filter(|e| counting || e.0.as_ref().is_none_or(|p| !matches!(**p, Plan::Counting))) {
            // a failed search stands only while the store has no path for the pair: the store grows as searches feed it
            // (`a_cached_failed_join_yields_to_a_stored_path`)
            from_store = if e.0.is_none() { stored(job) } else { None };
            if from_store.is_none() {
                replay(job, &e.1);
                job.join_cost.hits += 1;
                return e.0.clone();
            }
        }
    }
    let mut examined = (memo_on || traced).then(hashbrown::HashSet::<Term>::default);
    let stored = if from_store.is_some() { from_store } else if memo_on { stored(job) } else { None };
    job.join_cost.stored += stored.is_some() as u64;
    let found = match stored {
        // a stored path's result rests on its terms, as a met search's on its path's: they and their subterms
        Some((plan, mut stack)) => {
            if let Some(x) = &mut examined {
                while let Some(q) = stack.pop() {
                    if let (true, Node::Op(_, l, r)) = (x.insert(q), *q.node()) {
                        stack.extend([l, r]);
                    }
                }
            }
            Some(plan)
        }
        // fed only where read, so what proofs search (memo off or a rule blocked) never reaches it
        None => join_search(job, a, b, &mut examined, memo_on),
    };
    if let Some(x) = examined {
        let trace = Trace::new(x.into_iter().map(|t| (t, Fired::Join)).collect());
        replay(job, &trace);
        if memo_on {
            job.rw.memo.as_mut().map(|m| m.joins.insert(key, std::rc::Rc::new((found.clone(), trace))));
        }
    }
    found
}

/// The path to the subterm a join step is at: that subterm's index in its term's preorder (0 the root, then the left
/// child's subterms, then the right's), so it holds at any depth (a bit per level in a `u64` lost the levels past 64:
/// run `2026-10-25-held-seen`). Going down reads the left child's size, so each step down takes the term it is in.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) struct StepPath {
    pub(super) at: u32,
}

impl StepPath {
    /// The path to the subterm `join_walk` is at (`up`).
    fn of(up: &JoinPlace) -> StepPath {
        StepPath { at: up.iter().map(|e| if e.3 { 1 + e.1.size() as u32 } else { 1 }).sum() }
    }
    /// Whether the path ends here: the subterm is the term itself.
    fn here(self) -> bool {
        self.at == 0
    }
    /// One level down (`!here()`) in a term whose left child is `a`: whether the path goes right, and the path from
    /// that child.
    fn down(self, a: Term) -> (bool, StepPath) {
        let left = a.size() as u32;
        if self.at <= left { (false, StepPath { at: self.at - 1 }) } else { (true, StepPath { at: self.at - 1 - left }) }
    }
    /// After a step at this path, `join_walk`'s path in child `right` of a term whose left child is `a`: None (skip it)
    /// for a child left of the path, and `Some(None)` for the rewritten subterm's children and those right of the path,
    /// which the walk takes whole.
    fn child(self, a: Term, right: bool) -> Option<Option<StepPath>> {
        if self.here() {
            return Some(None);
        }
        let (on, next) = self.down(a);
        if on == right { Some(Some(next)) } else { right.then_some(None) }
    }
}

/// A join step from the reached term `from`: the step `table.join[eq]` at the subterm at `path`. The search keeps these
/// and makes plans only on the path that meets.
#[derive(Clone, Copy)]
pub(super) struct JoinStep {
    pub(super) from: Term,
    pub(super) path: StepPath,
    pub(super) eq: u32,
}

impl JoinStep {
    /// The step `eq` from `from` at the subterm `join_walk` is at (`up`).
    pub(super) fn new(from: Term, up: &JoinPlace, eq: usize) -> JoinStep {
        JoinStep { from, path: StepPath::of(up), eq: eq as u32 }
    }
    /// The term the step reaches, its rewritten subterm `at` made.
    pub(super) fn spine(self, at: Term) -> Spine {
        Spine { from: self.from, path: self.path, at }
    }
    /// The order of `join_walk` at `t`, the term the step reached: its path, unless the step shrank the term. A skipped
    /// step's other order passes a middle term of `size(t) - Δ + δ` (`Δ` this step's size change, `δ` the skipped one's)
    /// against the end term's `size(t) + δ`, so with `Δ >= 0` the cap stops neither and the search reaches the same terms
    /// (docs/tier-cycle.md, "Making the picks less sensitive").
    pub(super) fn order(self, t: Term) -> Option<StepPath> {
        (t.size() >= self.from.size()).then_some(self.path)
    }
}

/// A term a join step reaches with its rewritten subterm made and the spine above it not: `from` with the subterm at
/// `path` replaced by `at`.
#[derive(Clone, Copy)]
pub(super) struct Spine {
    from: Term,
    path: StepPath,
    at: Term,
}

impl Spine {
    /// One level down the path (`!path.here()`): the root's operator, its child off the path, whether the path goes right,
    /// and the spine from the child on it.
    fn down(self) -> (usize, Term, bool, Spine) {
        let Node::Op(o, a, b) = *self.from.node() else { unreachable!("a step's path stays in the term") };
        let (right, path) = self.path.down(a);
        (o, if right { a } else { b }, right, Spine { from: if right { b } else { a }, path, at: self.at })
    }
    pub(super) fn make(self) -> Term {
        if self.path.here() {
            return self.at;
        }
        let (o, off, right, next) = self.down();
        let u = next.make();
        if right { Term::op(o, off, u) } else { Term::op(o, u, off) }
    }
    /// Whether `u` is this term: down `u` along the path, the children off it and then `at` compared by pointer.
    pub(super) fn is(mut self, mut u: Term) -> bool {
        while !self.path.here() {
            let (o, off, right, next) = self.down();
            match *u.node() {
                Node::Op(q, l, r) if q == o && (if right { l } else { r }) == off => u = if right { r } else { l },
                _ => return false,
            }
            self = next;
        }
        u == self.at
    }
    /// Whether this is `subst_pat(p, sub)`: down the pattern and the path together, then `is_subst` or `is` where one
    /// ends.
    fn is_pat(self, p: &Term, sub: &[Option<Term>]) -> bool {
        if self.path.here() {
            return is_subst(self.at, p, sub);
        }
        match *p.node() {
            Node::V(i) => sub[i].is_some_and(|t| self.is(t)),
            Node::Op(o, pa, pb) => {
                let (q, off, right, next) = self.down();
                o == q && if right { is_subst(off, &pa, sub) && next.is_pat(&pb, sub) } else { is_subst(off, &pb, sub) && next.is_pat(&pa, sub) }
            }
            _ => false,
        }
    }
    /// Whether this is the term at `up`'s root with the subterm at `up` replaced by `subst_pat(p, sub)`: down both paths
    /// while they agree; where they part, each side's child off its path against the other's; where one ends, `is_step`
    /// or `is_pat`.
    pub(super) fn is_step(mut self, up: &JoinPlace, p: &Term, sub: &[Option<Term>]) -> bool {
        for (i, &(o, a, b, right)) in up.iter().enumerate() {
            if self.path.here() {
                return is_step(self.at, &up[i..], p, sub);
            }
            let (q, off, r, next) = self.down();
            let mine = if right { a } else { b };
            if o != q {
                return false;
            }
            if r != right {
                return next.is(mine) && is_step(off, &up[i + 1..], p, sub);
            }
            if off != mine {
                return false;
            }
            self = next;
        }
        self.is_pat(p, sub)
    }
}

/// Where `join_walk` is in a term: each ancestor of the subterm it is at, as its operator, children and whether the walk
/// went right.
type JoinPlace = [(usize, Term, Term, bool)];

/// `t`'s join steps of at most `cap` nodes in all, in order: those at the root by `table.join`, then those in the left
/// child, then the right; each passed to `visit` with its place, subterm, step index and match, while `visit` returns
/// true; a rule whose `Need` is over the cap, or that is `blocked` (being proved), is skipped unmatched. Adds the subterms it walks to `examined`.
/// After a step (`order`), only one order of two steps at disjoint places is walked: the subtrees left of the step's path
/// are skipped, as a step there and this one, the other taken first, reach the same term. `join_search` orders the walk
/// only after a step that did not shrink the term (`JoinStep::order`), where the cap cannot stop the other order's middle
/// term, so a search reaches the same terms at each depth as unordered: the same rules and M on salts 1-5, 6% less search
/// time (docs/tier-cycle.md, "The order made exact").
#[allow(clippy::too_many_arguments)]
pub(super) fn join_walk(
    t: Term,
    order: Option<StepPath>,
    table: &RuleTable,
    blocked: &[RuleKey],
    cap: usize,
    up: &mut Vec<(usize, Term, Term, bool)>,
    examined: &mut Option<hashbrown::HashSet<Term>>,
    visit: &mut impl FnMut(&JoinPlace, Term, usize, &[Option<Term>; RULE_VARS], usize) -> bool,
) -> bool {
    crate::work::count(crate::work::Site::Walk);
    if let Some(x) = examined {
        x.insert(t);
    }
    let size = t.size();
    let room = cap as isize - size as isize;
    for (i, need) in table.join_index.get(&t) {
        if need.skips(room, cap as isize) {
            continue;
        }
        let e = &table.join[i];
        let mut sub = [None; RULE_VARS];
        if match_pat(&e.from, &t, &mut sub) && !blocked.iter().any(|&(l, r)| (l, r) == (e.lhs, e.rhs)) && !visit(up, t, i, &sub, cap) {
            return false;
        }
    }
    if let Node::Op(o, a, b) = *t.node() {
        for (right, c) in [(false, a), (true, b)] {
            let Some(order) = order.map_or(Some(None), |p| p.child(a, right)) else { continue };
            up.push((o, a, b, right));
            let go = join_walk(c, order, table, blocked, cap - (size - c.size()), up, examined, visit);
            up.pop();
            if !go {
                return false;
            }
        }
    }
    true
}

/// `(sh, size)` of `subst_pat(p, sub)`, without making it.
pub(super) fn subst_sig(p: &Term, sub: &[Option<Term>]) -> (u64, usize) {
    match *p.node() {
        Node::V(i) => sub[i].map(|s| (s.sh(), s.size())).expect("bound"),
        Node::Op(o, a, b) => {
            let ((ha, za), (hb, zb)) = (subst_sig(&a, sub), subst_sig(&b, sub));
            (sh_op(o, ha, hb), 1 + za + zb)
        }
        _ => (p.sh(), 1),
    }
}

/// Whether `t` is `subst_pat(p, sub)`.
fn is_subst(t: Term, p: &Term, sub: &[Option<Term>]) -> bool {
    match (*p.node(), *t.node()) {
        (Node::V(i), _) => sub[i] == Some(t),
        (Node::Op(o, pa, pb), Node::Op(q, a, b)) => o == q && is_subst(a, &pa, sub) && is_subst(b, &pb, sub),
        (Node::Op(..), _) => false,
        _ => t == *p,
    }
}

/// The `sh` of the term at `up`'s root with the subterm at `up` replaced by one of `sh` `h`, without making it.
pub(super) fn place_sh(up: &JoinPlace, h: u64) -> u64 {
    up.iter().rev().fold(h, |h, &(o, a, b, right)| if right { sh_op(o, a.sh(), h) } else { sh_op(o, h, b.sh()) })
}

/// Whether `t` is the term at `up`'s root with the subterm at `up` replaced by `subst_pat(p, sub)`.
pub(super) fn is_step(mut t: Term, up: &JoinPlace, p: &Term, sub: &[Option<Term>]) -> bool {
    for &(o, a, b, right) in up {
        match *t.node() {
            Node::Op(q, l, r) if q == o && (if right { l == a } else { r == b }) => t = if right { r } else { l },
            _ => return false,
        }
    }
    is_subst(t, p, sub)
}

/// The plan of `step.from = ` the term the step reaches.
fn step_plan(job: &Job, step: &JoinStep) -> PlanRc {
    let (mut up, mut x, mut path) = (vec![], step.from, step.path);
    while !path.here() {
        let Node::Op(o, a, b) = *x.node() else { unreachable!("a step's path stays in the term") };
        let right;
        (right, path) = path.down(a);
        up.push((o, a, b, right));
        x = if right { b } else { a };
    }
    let e = &job.rules().table.join[step.eq as usize];
    let mut sub = [None; RULE_VARS];
    assert!(match_pat(&e.from, &x, &mut sub), "a step's law matches where it was found");
    let law = Plan::law(job, e.kind, e.lhs, e.rhs, sub[..e.vars].iter().map(|s| s.unwrap_or(Term::v(0))).collect());
    let p = if e.backward { Plan::sym(job, law) } else { law };
    up.iter().rev().fold(p, |p, &(o, a, b, right)| if right { Plan::cong(job, o, Plan::refl(job, &a), p) } else { Plan::cong(job, o, p, Plan::refl(job, &b)) })
}

/// A term `join_search` reached: a side's own, or the step it was reached by with that step's rewritten subterm, the
/// spine above it made only when the search expands it or its path meets.
#[derive(Clone, Copy)]
pub(super) enum Reached {
    Side(Term),
    Step(JoinStep, Term),
}

impl Reached {
    pub(super) fn make(self) -> Term {
        match self {
            Reached::Side(t) => t,
            Reached::Step(step, at) => step.spine(at).make(),
        }
    }
    pub(super) fn is(self, u: Term) -> bool {
        match self {
            Reached::Side(t) => t == u,
            Reached::Step(step, at) => step.spine(at).is(u),
        }
    }
    /// Whether this is the term at `up`'s root with the subterm at `up` replaced by `subst_pat(p, sub)`.
    pub(super) fn is_step(self, up: &JoinPlace, p: &Term, sub: &[Option<Term>]) -> bool {
        match self {
            Reached::Side(t) => is_step(t, up, p, sub),
            Reached::Step(step, at) => step.spine(at).is_step(up, p, sub),
        }
    }
    fn step(self) -> Option<JoinStep> {
        match self {
            Reached::Side(_) => None,
            Reached::Step(step, _) => Some(step),
        }
    }
}

/// `join_eq`'s search, adding the terms it examined to `examined`. A step's term is looked up among those reached by its
/// `sh` and `is_step` before anything is made, so only new terms' rewritten subterms are made (58% of a cmp3d mine's steps
/// reached a term its side had: docs/tier-cycle.md, "Lazy join steps"); the spine above one is made only when the search
/// expands it or its path meets (36.8% of new terms were expanded: "What the join's duplicates and term building are"),
/// and plans only on the path that meets. With `feed`, a met path goes to the store the job feeds.
fn join_search(job: &mut Job, a: &Term, b: &Term, examined: &mut Option<hashbrown::HashSet<Term>>, feed: bool) -> Option<PlanRc> {
    let (cap, visit, t0) = (a.size().max(b.size()) + 2, join_visit(job), std::time::Instant::now());
    // each reached term by its `sh`
    type Seen = hashbrown::HashTable<(u64, Reached)>;
    let get = |seen: &Seen, t: Term| seen.find(t.sh(), |e| e.0 == t.sh() && e.1.is(t)).expect("reached").1.step();
    let path = |seen: &Seen, mut t: Term| -> PlanRc {
        let mut steps = vec![];
        while let Some(step) = get(seen, t) {
            steps.push(step_plan(job, &step));
            t = step.from;
        }
        steps.into_iter().rev().reduce(|a, b| Plan::trans(job, a, b)).unwrap_or_else(|| Plan::refl(job, &t))
    };
    let mut seen: [Seen; 2] = [Seen::new(), Seen::new()];
    for (side, t) in [(0, a), (1, b)] {
        seen[side].insert_unique(t.sh(), (t.sh(), Reached::Side(*t)), |e| e.0);
    }
    // each side's reached terms with their depth, and those not yet expanded by (depth plus size, index): least first, in
    // the order reached among equals
    let mut store = [vec![(Reached::Side(*a), 0)], vec![(Reached::Side(*b), 0)]];
    let mut pending: [BinaryHeap<Reverse<(usize, usize)>>; 2] = [BinaryHeap::from([Reverse((a.size(), 0))]), BinaryHeap::from([Reverse((b.size(), 0))])];
    let table = &*job.rules().table;
    let mut met_path: Vec<(Term, StoredStep)> = vec![];
    let found = (|| {
        let mut up = vec![];
        while !pending[0].is_empty() && !pending[1].is_empty() && seen[0].len() + seen[1].len() <= visit {
            let s = (pending[0].len() > pending[1].len()) as usize;
            let Reverse((_, i)) = pending[s].pop().expect("pending");
            let (r, depth) = store[s][i];
            let t = r.make();
            let mut met = None;
            let (here, there) = seen.split_at_mut(1);
            let (mine, other) = if s == 0 { (&mut here[0], &there[0]) } else { (&mut there[0], &here[0]) };
            let order = r.step().and_then(|s| s.order(t));
            join_walk(t, order, table, &job.blocked, cap, &mut up, examined, &mut |up, x, eq, sub, cap| {
                let e = &table.join[eq];
                let (h, size) = subst_sig(&e.to, sub);
                if size > cap || h == x.sh() && is_subst(x, &e.to, sub) {
                    return true;
                }
                let h = place_sh(up, h);
                let step = JoinStep::new(t, up, eq);
                if let Some(&(_, u)) = other.find(h, |c| c.0 == h && c.1.is_step(up, &e.to, sub)) {
                    met = Some((step, u));
                    return false;
                }
                if mine.find(h, |c| c.0 == h && c.1.is_step(up, &e.to, sub)).is_none() {
                    let r = Reached::Step(step, subst_pat(&e.to, sub));
                    mine.insert_unique(h, (h, r), |c| c.0);
                    pending[s].push(Reverse((depth + 1 + t.size() + size - x.size(), store[s].len())));
                    store[s].push((r, depth + 1));
                }
                true
            });
            let Some((step, u)) = met else { continue };
            let u = u.make();
            // the path's steps, for the store the job feeds
            if feed {
                let kept = |s: &JoinStep| {
                    let e = &table.join[s.eq as usize];
                    StoredStep { from: s.from, path: s.path, law: (e.lhs, e.rhs, e.backward) }
                };
                met_path.push((u, kept(&step)));
                for (side, mut p) in [(&seen[s], t), (&seen[1 - s], u)] {
                    while let Some(prev) = get(side, p) {
                        met_path.push((p, kept(&prev)));
                        p = prev.from;
                    }
                }
            }
            // a met search's result rests on its path only: keep what was examined at the path's terms
            if let Some(x) = examined {
                x.clear();
                let mut stack = vec![u];
                for (side, mut p) in [(&seen[s], t), (&seen[1 - s], u)] {
                    stack.push(p);
                    while let Some(prev) = get(side, p) {
                        p = prev.from;
                        stack.push(p);
                    }
                }
                // with their subterms
                while let Some(q) = stack.pop() {
                    if let (true, Node::Op(_, l, r)) = (x.insert(q), *q.node()) {
                        stack.extend([l, r]);
                    }
                }
            }
            // `this side = u` and `other side = u`
            let (here, there) = (Plan::trans(job, path(&seen[s], t), step_plan(job, &step)), path(&seen[1 - s], u));
            let (pa, pb) = if s == 0 { (here, there) } else { (there, here) };
            return Some(Plan::trans(job, pa, Plan::sym(job, pb)));
        }
        None
    })();
    let (reached, nanos) = ((seen[0].len() + seen[1].len()) as u64, t0.elapsed().as_nanos() as u64);
    if let Some(JoinStoreUse::Feed(st)) = job.join_store.as_mut() {
        for (to, step) in met_path {
            st.add(to, step);
        }
    }
    let c = &mut job.join_cost;
    (c.searches, c.reached, c.met, c.nanos) = (c.searches + 1, c.reached + reached, c.met + found.is_some() as u64, c.nanos + nanos);
    c.failed_nanos += if found.is_some() { 0 } else { nanos };
    found
}

