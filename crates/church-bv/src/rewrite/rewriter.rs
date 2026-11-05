use super::*;

impl Trace {
    pub fn new(items: Vec<(Term, Fired)>) -> Trace {
        let shapes = items.iter().fold(0, |m, (t, _)| m | t.shape());
        Trace { items, shapes }
    }

    pub fn items(&self) -> &[(Term, Fired)] {
        &self.items
    }

    /// Whether `rule` could act on some term of the trace on which `also` holds of the rule that fired: its left side matches it,
    /// or, on a term the join examined, its right side does where the rule is a join step backward (`join_usable`).
    pub fn touched_by(&self, (l, r): &(Term, Term), also: impl Fn(&Fired) -> bool) -> bool {
        let fits = |p: &Term| self.shapes & p.needs() == p.needs();
        let (fl, fr) = (fits(l), fits(r) && join_usable(r, l));
        (fl || fr) && self.items.iter().any(|(t, f)| (fl && matches(l, t) || fr && *f == Fired::Join && matches(r, t)) && also(f))
    }
}

/// Many traces' terms for `Trace::touched_by` over all of them at once: each distinct (term, fired) once, with the traces it
/// is in, grouped by the term's shape. The rule miner asks which of every law's traces each candidate touches (`affected`),
/// and the same terms recur across the laws' traces.
pub struct TraceIndex {
    groups: Vec<(u64, Vec<Indexed>)>,
}

/// A distinct trace item and the traces it is in, ascending.
type Indexed = (Term, Fired, Vec<usize>);

impl TraceIndex {
    pub fn new<'a>(traces: impl IntoIterator<Item = &'a Trace>) -> TraceIndex {
        let mut at: hashbrown::HashMap<(Term, Fired), Vec<usize>> = Default::default();
        for (i, tr) in traces.into_iter().enumerate() {
            for item in &tr.items {
                let v = at.entry(*item).or_default();
                if v.last() != Some(&i) {
                    v.push(i);
                }
            }
        }
        let mut groups: hashbrown::HashMap<u64, Vec<Indexed>> = Default::default();
        for ((t, f), v) in at {
            groups.entry(t.shape()).or_default().push((t, f, v));
        }
        TraceIndex { groups: groups.into_iter().collect() }
    }

    /// The traces, ascending, whose `touched_by(rule, also)` holds. A term's shape has every bit a pattern needs where the
    /// pattern matches it (`Term::shape`), so only those groups are scanned.
    pub fn touched(&self, (l, r): &(Term, Term), also: impl Fn(&Fired) -> bool) -> Vec<usize> {
        let back = join_usable(r, l);
        let (nl, nr) = (l.needs(), r.needs());
        let mut out = vec![];
        for (shape, items) in &self.groups {
            let (fl, fr) = (shape & nl == nl, back && shape & nr == nr);
            if !(fl || fr) {
                continue;
            }
            for (t, f, v) in items {
                if (fl && matches(l, t) || fr && *f == Fired::Join && matches(r, t)) && also(f) {
                    out.extend_from_slice(v);
                }
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }
}

/// A cached `rewrite`: the result and what the call did besides returning it, so that a hit can replay it.
pub(super) struct Rewritten {
    out: (Term, PlanRc),
    /// rule steps used (`RewriteState::budget`): a hit needs at least this many left
    steps: i64,
    fallbacks: u64,
    /// the terms `rule_step` was asked about and whether a rule fired (`RewriteState::trace`), when `traced` (the trace was on)
    trace: Trace,
    traced: bool,
    /// the terms the call took up below its own (`RewriteState::rewrote`), once each: a replay is right only where the path cuts none of them
    rewrote: Vec<Term>,
}

/// While `Some`, `rewrite` calls over `k` variables are cached by (width, term). The rule miner sets it for one rule set
/// (one `score_laws` call): the result of `rewrite` is a function of the term, the rules in force and the budget left, so a repeat
/// under the same rules is a hit. Calls over other variable counts (the generalization path adds witnesses) are not cached.
/// `joins` caches `join_eq` by pair, with the trace that invalidates it: a failed search's examined terms, a met one's path.
pub struct RewriteMemo {
    pub(super) k: usize,
    pub(super) map: hashbrown::HashMap<(usize, Term), std::rc::Rc<Rewritten>>,
    pub(super) joins: hashbrown::HashMap<(Term, Term), std::rc::Rc<Joined>>,
}

/// A memoized `join_eq`: its plan (`None` if the search failed) and its trace.
type Joined = (Option<PlanRc>, Trace);

impl RewriteMemo {
    pub fn new(k: usize) -> RewriteMemo {
        RewriteMemo { k, map: Default::default(), joins: Default::default() }
    }

    /// The traced entries whose traces `keep` accepts. A rule tried after the others changes no entry whose trace it matches
    /// nowhere among the terms no rule fired on, nor a join that examined no term it touches (`Trace::touched_by`), so the rule
    /// miner seeds each evaluation of a chosen set with the last one's entries that the rules in or out cannot change.
    pub fn filtered(&self, keep: impl Fn(&Trace) -> bool) -> RewriteMemo {
        // presized to the whole memo (an upper bound): grown from empty, the map rehashed several times per evaluation
        let mut map = hashbrown::HashMap::with_capacity(self.map.len());
        map.extend(self.map.iter().filter(|(_, e)| e.traced && keep(&e.trace)).map(|(k, e)| (*k, e.clone())));
        let mut joins = hashbrown::HashMap::with_capacity(self.joins.len());
        joins.extend(self.joins.iter().filter(|(_, e)| keep(&e.1)).map(|(k, e)| (*k, e.clone())));
        RewriteMemo { k: self.k, map, joins }
    }
}

/// The step budget one law gets in the probes, `law_cost` and the rewriting tests (`Job::measured`).
pub const LAW_STEPS: i64 = 200;
/// A budget no rewrite reaches: a job's own outside a measured call.
pub const UNBOUNDED: i64 = i64::MAX / 2;

/// A job's rewriting in progress (`Job::rw`). `proving` swaps in a fresh one for a rule's proof.
pub struct RewriteState {
    /// the terms `rewrite` is working on, outermost first
    pub path: Vec<Term>,
    /// the terms `rewrite` took up (pushed on the path) since the outermost call began, memo replays included
    pub rewrote: Vec<Term>,
    /// the lowest path index a cut matched since the innermost `rewrite_memo` miss began (`usize::MAX`: none)
    pub cut_low: usize,
    /// how many calls `rewrite` cut so far
    pub cycle_cuts: u64,
    pub memo: Option<RewriteMemo>,
    /// While `Some`, `rule_step` records every term it is asked to rewrite, and whether a rule fired on it: a rule added anywhere
    /// in the rule list can change a rewriting only if its left side matches one of them, and one added last only if it matches
    /// one where no rule fired.
    pub trace: Option<Vec<(Term, Fired)>>,
    /// How many more rule applications `rule_step` may make; the rule miner sets it per trial so that a candidate that
    /// undoes a built-in rule cannot loop. Soundness is unaffected: a refused step only leaves the term less normalized.
    pub budget: i64,
    /// How many times `prove_eq` closed a pair with a whole-term machine proof (the rewriting did not finish the job). Per
    /// job, so that the parallel miner's workers each read their own before/after difference.
    pub fallbacks: u64,
}

impl Default for RewriteState {
    fn default() -> RewriteState {
        RewriteState { path: vec![], rewrote: vec![], cut_low: usize::MAX, cycle_cuts: 0, memo: None, trace: None, budget: UNBOUNDED, fallbacks: 0 }
    }
}

/// `s` homeomorphically embeds in `t`: `t` is `s` with nodes inserted (Kruskal). Between terms of equal size it is equality,
/// and a larger term never embeds. Each pair of subterms is decided once (`seen`), so a call takes at most |subterms of `s`|
/// x |subterms of `t`| steps; the plain recursion took exponentially many on chains of one operator
/// (`embedding_long_chains_finishes`).
pub(super) fn embeds(s: &Term, t: &Term) -> bool {
    fn go(s: Term, t: Term, seen: &mut hashbrown::HashMap<(Term, Term), bool>) -> bool {
        if s.size() >= t.size() {
            return s == t;
        }
        if let Some(&e) = seen.get(&(s, t)) {
            return e;
        }
        let Node::Op(g, t1, t2) = *t.node() else { unreachable!("a term larger than another is an Op") };
        let e = matches!(*s.node(), Node::Op(f, s1, s2) if f == g && go(s1, t1, seen) && go(s2, t2, seen)) || go(s, t1, seen) || go(s, t2, seen);
        seen.insert((s, t), e);
        e
    }
    // the cut's path holds mostly terms larger than `t`, settled here without a map: with a map (and its hasher's seed)
    // for every call `embeds` was 1.64% of a sweep, without 0.51% (runs `2026-10-28-embeds-prof` and `-embeds-prof2`)
    if s.size() >= t.size() {
        return s == t;
    }
    go(*s, *t, &mut hashbrown::HashMap::new())
}

/// `t` (over `k` variables) rewritten bottom-up, with the plan of `t = t'` (`Compiler` proves it). Rewriting is deterministic apart from
/// the step budget, so a call `rewrite(t)` made while `t` itself is being rewritten further out can only repeat that work until the
/// budget runs out: a rewrite cycle. A chain that returns to a larger copy of a term it is rewriting (one that term embeds in) is
/// taken to grow without end. The cut returns `t` unchanged in both cases, so the chain ends one lap round instead of at the budget
/// (docs/tier-cycle/, "Cycle cut").
pub fn rewrite(job: &mut Job, t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    if !matches!(*t.node(), Node::Op(..)) {
        return rewrite_memo(job, t, n, k);
    }
    if let Some(i) = cut_at(&job.rw.path, t) {
        job.rw.cut_low = job.rw.cut_low.min(i);
        job.rw.cycle_cuts += 1;
        return (*t, Plan::refl(job, t));
    }
    job.rw.path.push(*t);
    job.rw.rewrote.push(*t);
    let out = rewrite_memo(job, t, n, k);
    if job.rw.path.pop().is_some() && job.rw.path.is_empty() {
        job.rw.rewrote.clear();
    }
    out
}

/// The cycle cut's test: `t` repeats, or grows from, a term on `path`.
fn cut_by(path: &[Term], t: &Term) -> bool {
    cut_at(path, t).is_some()
}

/// The index of the innermost term on `path` that cuts `t`.
fn cut_at(path: &[Term], t: &Term) -> Option<usize> {
    path.iter().rposition(|s| embeds(s, t))
}

fn rewrite_memo(job: &mut Job, t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    let on = matches!(*t.node(), Node::Op(..)) && job.rw.memo.as_ref().is_some_and(|m| m.k == k);
    if !on {
        return rewrite_uncached(job, t, n, k);
    }
    let key = (n, *t);
    let hit = job.rw.memo.as_ref().and_then(|m| m.map.get(&key).cloned());
    // the entry was made with no cut against a term further out, so the path in force now must cut none of the terms it took up
    // either; and one made while counting has no plan to give a caller that is not
    let counting = job.rules().score_only;
    let fits = |c: &Rewritten| {
        job.rw.budget >= c.steps
            && (counting || !matches!(*c.out.1, Plan::Counting))
            && !c.rewrote.iter().any(|v| cut_by(&job.rw.path, v))
    };
    if let Some(c) = hit.filter(|c| fits(c)) {
        if cfg!(debug_assertions) {
            check_replay(job, t, n, k, &c);
        }
        job.rw.budget -= c.steps;
        job.rw.fallbacks += c.fallbacks;
        if let Some(v) = job.rw.trace.as_mut() {
            v.extend_from_slice(c.trace.items());
        }
        job.rw.rewrote.extend(c.rewrote.iter().copied());
        return c.out.clone();
    }
    let (budget0, fallbacks0, trace0) = (job.rw.budget, job.rw.fallbacks, job.rw.trace.as_ref().map(|v| v.len()));
    let (plen, low0, rewrote0) = (job.rw.path.len(), std::mem::replace(&mut job.rw.cut_low, usize::MAX), job.rw.rewrote.len());
    let out = rewrite_uncached(job, t, n, k);
    let (budget1, low) = (job.rw.budget, job.rw.cut_low);
    job.rw.cut_low = low0.min(low);
    // a call that ran the budget out was cut short by it: its result depends on the budget it started with. One with a cycle cut
    // against a term further out than `t` (`rewrite` pushed `t` at `plen - 1`) depends on that term; cuts against `t` or terms
    // taken up below it come back on any replay, and no new cut can, since a path that cuts a term in `rewrote` is never replayed
    if budget1 > 0 && low.saturating_add(1) >= plen {
        let trace = Trace::new(job.rw.trace.as_ref().map(|v| v[trace0.unwrap_or(0)..].to_vec()).unwrap_or_default());
        // once each, in address order (a replay only asks whether the path cuts any of them); a fresh set per entry grew and
        // rehashed for 2.2% of a sweep (docs/tier-cycle/, "Survey: the next lever")
        let mut rewrote = job.rw.rewrote[rewrote0..].to_vec();
        rewrote.sort_unstable_by_key(|t| t.addr());
        rewrote.dedup();
        let entry = Rewritten { out: out.clone(), steps: budget0 - budget1, fallbacks: job.rw.fallbacks - fallbacks0, trace, traced: trace0.is_some(), rewrote };
        if let Some(m) = job.rw.memo.as_mut() {
            m.map.insert(key, std::rc::Rc::new(entry));
        }
    }
    out
}

/// Debug builds: a memo hit about to be replayed is redone without the memo, under the same path and budget, and must match it
/// (the law 168 bug was a replay a fresh rewrite would have cut). Release builds compile it too, so it cannot rot unseen.
fn check_replay(job: &mut Job, t: &Term, n: usize, k: usize, c: &Rewritten) {
    let memo = std::mem::take(&mut job.rw.memo);
    let trace = std::mem::take(&mut job.rw.trace);
    let (budget, fallbacks, cuts, low, rewrote) = (
        job.rw.budget,
        job.rw.fallbacks,
        job.rw.cycle_cuts,
        job.rw.cut_low,
        job.rw.rewrote.len(),
    );
    let fresh = rewrite_uncached(job, t, n, k);
    let (steps, fresh_fallbacks) = (budget - job.rw.budget, job.rw.fallbacks - fallbacks);
    job.rw.memo = memo;
    job.rw.trace = trace;
    job.rw.budget = budget;
    job.rw.fallbacks = fallbacks;
    job.rw.cycle_cuts = cuts;
    job.rw.cut_low = low;
    job.rw.rewrote.truncate(rewrote);
    let show = |(t, s, f): (Term, i64, u64)| format!("{} in {s} steps, {f} fallbacks", t.show());
    assert!(
        (fresh.0, steps, fresh_fallbacks) == (c.out.0, c.steps, c.fallbacks),
        "memo replay of {}: {} where a fresh rewrite gives {}",
        t.show(),
        show((c.out.0, c.steps, c.fallbacks)),
        show((fresh.0, steps, fresh_fallbacks))
    );
}

fn rewrite_uncached(job: &mut Job, t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    let Node::Op(o, a, b) = *t.node() else { return (*t, Plan::refl(job, t)) };
    // children first: trying the library rules on a node before its children are normalized raised M 3x (docs/tier-cycle/, "Rule order")
    let ((a2, pa), (b2, pb)) = (rewrite(job, &a, n, k), rewrite(job, &b, n, k));
    let cong = Plan::cong(job, o, pa, pb);
    let t1 = Term::op(o, a2, b2);
    // the class table's normal form (docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md §5): a node the
    // table knows is final, as its own representative or through the proved step to it; any other node goes on to the
    // rules (over a fourth variable, a class not stored, or a replacement with no proof)
    if !job.setup().ablated("classes") {
        let c = crate::classes::Classes::get();
        if let Some(r) = c.lookup(&t1) {
            if r == t1 {
                return (t1, cong);
            }
            if let Some((r, p)) = c.step(job, n, k, &t1) {
                return (r, Plan::trans(job, cong, p));
            }
        }
    }
    if o != ADD {
        // the library rules first (`shldist`, ...)
        if let Some((target, step)) = rule_step(job, &t1) {
            let (t3, p3) = rewrite(job, &target, n, k);
            return (t3, Plan::trans(job, Plan::trans(job, cong, step), p3));
        }
        if matches!(o, SUB | LT | SHL1 | SHR1) {
            return (t1, cong);
        }
        // bitwise and shift terms only: a node equal to 0, -1 or one of its own subterms collapses to it, by the
        // per-position prover (the truth-table collapse below treats a shift as an atom)
        if let (false, true, true) = (job.setup().ablated("collapse"), t1.add_free(), t1.has_shift()) {
            let mut subs = vec![];
            t1.subterms(&mut subs);
            let cands = [Term::ZERO, Term::ONES].into_iter().chain(subs.into_iter().skip(1).filter(|c| c.size() < t1.size()));
            if let Some(c) = cands.into_iter().find(|c| c.add_free() && t1.is_law(c, k)) {
                return (c, Plan::trans(job, cong, Plan::law(job, LawKind::Bitwise, t1, c, vars(k))));
            }
        }
        // a bitwise node equal to 0, -1 or one of its atoms collapses to it (truth table, then `bitwise_law`)
        let mut atoms = vec![];
        if let (false, Some(abs)) = (job.setup().ablated("collapse"), abstract_atoms(&t1, &mut atoms, k)) {
            let truth = |t: &Term| (0..1usize << k).map(|m| term_gb(&Bools, t, &(0..k).map(|v| m >> v & 1 == 1).collect::<Vec<_>>())).collect::<Vec<_>>();
            let want = truth(&abs);
            let cands: Vec<Term> = [Term::ZERO, Term::ONES].into_iter().chain((0..k).map(Term::v)).collect();
            if let Some(c) = cands.iter().find(|c| c.max_var() < atoms.len().max(1) && truth(c) == want) {
                let target = if let Node::V(i) = *c.node() { atoms[i] } else { *c };
                if target != t1 {
                    let args = (0..k).map(|i| atoms.get(i).cloned().unwrap_or(Term::v(0))).collect();
                    return (target, Plan::trans(job, cong, Plan::law(job, LawKind::Bitwise, abs, *c, args)));
                }
            }
        }
        // commutative operands in a fixed order (text order, constants last: 0 before -1), by the generic bitwise law
        let constant = |t: &Term| match *t.node() {
            Node::Zero => Some(0),
            Node::Ones => Some(1),
            _ => None,
        };
        let before = match (constant(&b2), constant(&a2)) {
            (None, None) => b2 < a2,
            (None, Some(_)) => true,
            (Some(_), None) => false,
            (Some(cb), Some(ca)) => cb < ca,
        };
        if before {
            let swap = |x: Term, y: Term| Term::op(o, x, y);
            let law = Plan::law(job, LawKind::Bitwise, swap(Term::v(0), Term::v(1)), swap(Term::v(1), Term::v(0)), vec![a2, b2]);
            return (swap(b2, a2), Plan::trans(job, cong, law));
        }
        return (t1, cong);
    }
    let sum = |p: &Term, q: &Term| Term::op(ADD, *p, *q);
    let (x, y, z) = (Term::v(0), Term::v(1), Term::v(2));
    let assoc = |job: &Job, p: &Term, q: &Term, r: &Term| Plan::law(job, LawKind::Assoc, sum(&sum(&x, &y), &z), sum(&x, &sum(&y, &z)), vec![*p, *q, *r]);
    let comm = |job: &Job, p: &Term, q: &Term| Plan::law(job, LawKind::Comm, sum(&x, &y), sum(&y, &x), vec![*p, *q]);
    // `x + 0` and `x + ~x` are the class table's (a constant-carry step, `chain`, was deleted as free with it on)
    let step = if let Some(r) = rule_step(job, &t1) {
        Some(r)
    } else if let (false, Node::Op(ADD, p, q)) = (job.setup().ablated("assoc"), *a2.node()) {
        // (p + q) + r = p + (q + r)
        Some((sum(&p, &sum(&q, &b2)), assoc(job, &p, &q, &b2)))
    } else if let (false, Node::Op(ADD, bp, bq)) = (job.setup().ablated("assoc") || job.setup().ablated("comm"), *b2.node()) {
        if bp < a2 {
            // a + (b + c) = (a + b) + c = (b + a) + c = b + (a + c)
            let (a_, b_, c_) = (&a2, &bp, &bq);
            let swapped = Plan::cong(job, ADD, comm(job, a_, b_), Plan::refl(job, c_));
            Some((sum(b_, &sum(a_, c_)), Plan::trans(job, Plan::trans(job, Plan::sym(job, assoc(job, a_, b_, c_)), swapped), assoc(job, b_, a_, c_))))
        } else {
            None
        }
    } else if !job.setup().ablated("comm") && b2 < a2 {
        Some((sum(&b2, &a2), comm(job, &a2, &b2)))
    } else {
        None
    };
    match step {
        None => (t1, cong),
        Some((t2, p)) => {
            let (t3, p3) = rewrite(job, &t2, n, k);
            (t3, Plan::trans(job, Plan::trans(job, cong, p), p3))
        }
    }
}

/// `t` with each variable and each non-bitwise subterm (`add`, `sub`, `lt`, a shift) replaced by an atom variable (up to `cap`, by `show`).
pub fn abstract_atoms(t: &Term, atoms: &mut Vec<Term>, cap: usize) -> Option<Term> {
    match *t.node() {
        Node::Zero | Node::Ones => Some(*t),
        Node::V(_) | Node::Op(ADD | SUB | LT | SHL1 | SHR1, ..) => {
            let i = match atoms.iter().position(|a| a == t) {
                Some(i) => i,
                None => {
                    atoms.push(*t);
                    atoms.len() - 1
                }
            };
            (i < cap).then_some(Term::v(i))
        }
        Node::Op(o, a, b) => Some(Term::op(o, abstract_atoms(&a, atoms, cap)?, abstract_atoms(&b, atoms, cap)?)),
    }
}

