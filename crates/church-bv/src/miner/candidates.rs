use super::*;

/// Whether a candidate left side `l` matches a subterm of the straggler's normalized terms.
pub(super) fn reaches(l: &Term, s: &Scored) -> bool {
    let mut subs = vec![];
    s.3[0].subterms(&mut subs);
    s.3[1].subterms(&mut subs);
    subs.iter().any(|t| matches(l, t))
}

/// The candidate rules for the stragglers (P3, P4), one per left side, and the other right sides of each left side (`rivals`).
pub(super) fn candidates(laws: &Laws, no_dup_lhs: bool, base: &[(Term, Term)], extra: &[(Term, Term)], loud: bool) -> (Vec<(Term, Term)>, hashbrown::HashMap<Term, Vec<(Term, Term)>>) {
    let (n, kv, stragglers) = (laws.n, laws.kv, &laws.stragglers);
    // the pool's rules go down in the rule order, ties broken by `tie_greater` (reassociation rules; section 70); the step
    // budget and the same-term check in `rule_step` still back up termination, and soundness is unaffected
    // goal-directed candidates: abstract each arithmetic subterm of a straggler's normalized terms into a pattern over
    // at most `POOL_VARS` variables (cutting subterms into variables), and look for a smaller term over the same variables
    // with the same values (`Pool`)
    let mut pool = Pool::new(n);
    if loud {
        println!("RULEMINER pool of {} terms, {} distinct functions", pool.terms, pool.index.len());
    }
    // patterns seen (`None`), and cross-side rules seen (`Some(rhs)`)
    let mut seen_pat: hashbrown::HashSet<(Term, Option<Term>)> = Default::default();
    let mut cands: Vec<(Term, Term)> = vec![];
    for st in stragglers {
        let mut subs = vec![];
        st.3[0].subterms(&mut subs);
        st.3[1].subterms(&mut subs);
        for sub in subs.iter().filter(|t| matches!(*t.node(), Node::Op(LT, ..)) || t.uses_add() && t.size() >= 3) {
            for (pat, _) in abstractions(sub, POOL_VARS) {
                let Node::Op(..) = *pat.node() else { continue };
                if !seen_pat.insert((pat, None)) || pat.size() > 9 {
                    continue;
                }
                for r in pool.equal(&pat).iter().filter(|r| rule_order_or_tie(&pat, r) && (0..POOL_VARS).all(|v| !r.has_var(v) || pat.has_var(v))) {
                    cands.push((pat, *r));
                }
            }
        }
    }
    // cross-side candidates: a subterm of one normalized side and a subterm of the other with the same value, both
    // abstracted by the same cuts (up to four variables): the rule `abstract(s) -> abstract(s')`
    for st in stragglers {
        let (mut sl, mut sr) = (vec![], vec![]);
        st.3[0].subterms(&mut sl);
        st.3[1].subterms(&mut sr);
        for (xs, ys) in [(&sl, &sr), (&sr, &sl)] {
            for x in xs.iter().filter(|t| t.uses_add() && t.size() >= 3 && t.size() <= 13) {
                for y in ys.iter().filter(|t| t.size() <= 13 && *t != x) {
                    if !(1..=4).all(|w| x.plausibly_equals(y, w, kv)) {
                        continue;
                    }
                    for (pat, cuts) in abstractions(x, CROSS_VARS) {
                        let Node::Op(..) = *pat.node() else { continue };
                        if cuts.len() <= 2 || pat.size() > 13 {
                            continue; // up to two variables is the pool route's job; at three both routes look (the pool's right sides are up to 5 nodes, these any size)
                        }
                        // express y with the same cuts, through placeholders V(4+j)
                        let mut yy = *y;
                        for (j, c) in cuts.iter().enumerate() {
                            yy = replace_term(&yy, c, &Term::v(4 + j));
                        }
                        // renumbered only when bare: a cut-free variable below 4 has no index to take
                        if !bare(&yy) {
                            continue;
                        }
                        let rhs = renum_placeholders(&yy);
                        // `x = y` holds for the straggler's variables, but the cuts become free variables, so the rule itself is checked:
                        // one that only held through a relation between the cuts would be scored every round and then fail its proof
                        if yy.size() < pat.size() + 4 && seen_pat.insert((pat, Some(rhs))) && (1..=4).all(|w| pat.plausibly_equals(&rhs, w, cuts.len())) {
                            // not ordered: orienting cross-side rules by the rule order raised M in every family (docs/tier-cycle/,
                            // "A rewrite cycle"); a growing one can cycle with the built-in rules until the step budget runs out
                            cands.push((pat, rhs));
                        }
                    }
                }
            }
        }
    }
    // extra candidates join the miner's own before the one-per-left-side pass
    cands.extend_from_slice(extra);
    // `RULEMINER_NODUPLHS` (default on, 0 = off): drop candidates whose left side already has a rule in force (`RULEMINER_BASE`); the one-per-left-side pass
    // below only sees this mine's candidates, so a later mine could otherwise add a second, competing rewrite for the same pattern
    if no_dup_lhs {
        let before = cands.len();
        let in_force: hashbrown::HashSet<&Term> = base.iter().map(|(l, _)| l).collect();
        cands.retain(|(l, _)| !in_force.contains(l));
        if loud {
            println!("RULEMINER dropped {} candidates whose left side is already in force", before - cands.len());
        }
    }
    // per left side, the smallest right side only, ties by `Term`'s order. Scoring every right side instead (each left side's rival
    // orientations) fixed add3's `sub` chains but raised M on cmp3d and sbo3 and made cmp3d's mine 4.5x slower (docs/tier-cycle/)
    // an identity (a pattern's pool group holds the pattern itself) never gains, and as the smallest right side it would displace
    // its left side's real candidates
    cands.retain(|(l, r)| l != r);
    cands.sort_by_key(|(l, r)| (l.size(), *l, r.size(), *r));
    cands.dedup();
    // rivals: the other right sides of each left side; a round's winner gives way to a rival that gains more on the same laws
    // (`Rounds::pick`; docs/tier-cycle/, "Preferences and rival orientations in the miner")
    let mut rivals: hashbrown::HashMap<Term, Vec<(Term, Term)>> = Default::default();
    for (l, r) in &cands {
        rivals.entry(*l).or_default().push((*l, *r));
    }
    rivals.values_mut().for_each(|v| {
        v.remove(0);
    });
    cands.dedup_by(|a, b| a.0 == b.0);
    if loud {
        println!("RULEMINER {} oriented candidates (one per left side)", cands.len());
    }
    (cands, rivals)
}

/// The pool route's variables: over three the miner finds small rules that carry to unseen laws (held-out M -6.9% against
/// two, docs/tier-cycle/, "A pool route over three variables finds them").
const POOL_VARS: usize = 3;

/// The pool route's terms: every term of up to 5 nodes over `POOL_VARS` variables and the constants, by their values on every
/// width-n input (4096 bytes a term over three variables at width 4); `lt` terms (one-bit values) only as roots over two terms
/// of up to 3 nodes, indexed apart so their 0/1 values never meet the n-bit constants.
pub(super) struct Pool {
    memo: ValueMemo<u8>,
    /// The terms by value class (`ValueMemo::class`), comparisons apart.
    index: hashbrown::HashMap<u32, Vec<Term>>,
    index_lt: hashbrown::HashMap<u32, Vec<Term>>,
    /// The terms outside `lt`.
    terms: usize,
}

impl Pool {
    pub(super) fn new(n: usize) -> Pool {
        let size = 5;
        let mut by_size: Vec<Vec<Term>> = vec![vec![]; size + 1];
        by_size[1] = (0..POOL_VARS).map(Term::v).chain([Term::ZERO, Term::ONES]).collect();
        for sz in 2..=size {
            let mut level = vec![];
            for x in &by_size[sz - 1] {
                level.push(Term::op(SHL1, *x, Term::ZERO));
                level.push(Term::op(SHR1, *x, Term::ZERO));
            }
            for i in 1..sz - 1 {
                for l in &by_size[i] {
                    for r in &by_size[sz - 1 - i] {
                        for o in [0usize, 1, 2, 3, 4] {
                            level.push(Term::op(o, *l, *r));
                        }
                    }
                }
            }
            by_size[sz] = level;
        }
        let mut pool = Pool { memo: ValueMemo::exhaustive(n, POOL_VARS), index: Default::default(), index_lt: Default::default(), terms: 0 };
        for t in by_size.iter().flatten() {
            pool.index.entry(pool.memo.class(t)).or_default().push(*t);
            pool.terms += 1;
        }
        for a in by_size.iter().take(4).flatten() {
            for b in by_size.iter().take(4).flatten() {
                let t = Term::op(LT, *a, *b);
                pool.index_lt.entry(pool.memo.class(&t)).or_default().push(t);
            }
        }
        pool
    }

    /// The pool's terms equal to `pat` (over at most `POOL_VARS` variables) on every input.
    pub(super) fn equal(&mut self, pat: &Term) -> &[Term] {
        let class = self.memo.class(pat);
        let index = if matches!(*pat.node(), Node::Op(LT, ..)) { &self.index_lt } else { &self.index };
        index.get(&class).map_or(&[], |g| g.as_slice())
    }
}

/// The patterns obtained from `t` by cutting subterms into variables: (pattern, cut subterms in variable order).
fn abstractions(t: &Term, cap: usize) -> Vec<(Term, Vec<Term>)> {
    let mut out = vec![];
    if !matches!(*t.node(), Node::Zero | Node::Ones) {
        out.push((Term::v(0), vec![*t]));
    } else {
        out.push((*t, vec![]));
    }
    if let Node::Op(o, a, b) = *t.node() {
        for (pa, ca) in abstractions(&a, cap) {
            for (pb, cb) in abstractions(&b, cap) {
                // renumber the right pattern's variables after the left's, merging equal cut subterms
                let mut cuts = ca.clone();
                let mut map = vec![];
                for c in &cb {
                    let at = cuts.iter().position(|x| x == c).unwrap_or_else(|| {
                        cuts.push(*c);
                        cuts.len() - 1
                    });
                    map.push(at);
                }
                if cuts.len() > cap {
                    continue;
                }
                out.push((Term::op(o, pa, renum_vars(&pb, &map)), cuts));
            }
        }
    }
    out.retain(|(_, c)| c.len() <= cap);
    out
}

/// `p` with each variable `i` renamed to `map[i]`.
fn renum_vars(p: &Term, map: &[usize]) -> Term {
    match *p.node() {
        Node::V(i) => Term::v(map[i]),
        Node::Op(o, a, b) => Term::op(o, renum_vars(&a, map), renum_vars(&b, map)),
        _ => *p,
    }
}

/// Whether every variable of `t` is a placeholder (`V(4+j)`).
fn bare(t: &Term) -> bool {
    match *t.node() {
        Node::V(i) => i >= 4,
        Node::Op(_, a, b) => bare(&a) && bare(&b),
        _ => true,
    }
}

/// `t` with each placeholder `V(4+j)` renamed to `V(j)`.
fn renum_placeholders(t: &Term) -> Term {
    match *t.node() {
        Node::V(i) => Term::v(i - 4),
        Node::Op(o, a, b) => Term::op(o, renum_placeholders(&a), renum_placeholders(&b)),
        _ => *t,
    }
}

