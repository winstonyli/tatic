use super::*;

/// What a job rewrites with (`Job::rules`, replaced only through `Job::with_rules`): the rule table and two switches.
/// Values, cheap to copy: the table is shared.
#[derive(Clone)]
pub struct Rules {
    /// The rules `rule_step` tries: the built-in ones, then those added at run time (by the rule miner) in `run_order`.
    pub(super) table: Rc<RuleTable>,
    /// Set where a plan is only counted: by the rule miner's scoring rounds, by its rule-set evaluations under
    /// `RULEMINER_FAST=1` or when the caller asks, and by tests that count. `prove_eq` then takes a machine fallback when a
    /// few tuples agree, without searching for its carry encoding, so a plan made under it may not compile.
    pub(super) score_only: bool,
    /// Print every rule application (the `normal_forms` debug test's `NF_TRACE`).
    trace_rules: bool,
}

impl Rules {
    /// The built-in rules of `setup` and the run-time rules `mined`, most specific first: larger left sides first, ties by
    /// text. `rule_step` applies the first rule that matches, so a library's order would otherwise change its normal forms:
    /// the same pooled library served in six orders gave total M 47-62 on add3 (docs/tier-cycle/, "Rule order"). Any
    /// order of the same rules now serves identically. Both switches off.
    pub fn new(setup: &Setup, mined: Vec<(Term, Term)>) -> Rules {
        Rules { table: Rc::new(RuleTable::sorted(setup, mined)), score_only: false, trace_rules: false }
    }

    /// These rules with the run-time rules `mined` instead; the switches stay.
    pub fn with_mined(&self, setup: &Setup, mined: Vec<(Term, Term)>) -> Rules {
        Rules { table: Rc::new(RuleTable::sorted(setup, mined)), ..self.clone() }
    }

    /// These rules, counting only (`score_only`) or not.
    pub fn counting(&self, on: bool) -> Rules {
        Rules { score_only: on, ..self.clone() }
    }

    /// These rules, printing every rule application or not.
    pub fn tracing(&self, on: bool) -> Rules {
        Rules { trace_rules: on, ..self.clone() }
    }

    /// The run-time rules, in the order they are tried.
    pub fn mined(&self) -> &[(Term, Term)] {
        &self.table.mined
    }

    pub fn score_only(&self) -> bool {
        self.score_only
    }

    /// Whether `other` is these same rules: the same table (not an equal copy), and the same switches.
    pub(crate) fn is(&self, other: &Rules) -> bool {
        Rc::ptr_eq(&self.table, &other.table) && (self.score_only, self.trace_rules) == (other.score_only, other.trace_rules)
    }
}

/// A rule as its two sides.
pub type RuleKey = (Term, Term);

/// `lhs -> rhs`, the spelling of rule files and logs.
pub fn rule_show((l, r): &RuleKey) -> String {
    format!("{} -> {}", l.show(), r.show())
}

/// A rule as `rule_step` tries it, with what does not depend on the term decided when the rule set is installed (deciding
/// it per term, and building the rule list per term, were about 10% of a sweep: docs/tier-cycle/, "Profile at f447a57").
#[derive(Clone, Copy)]
pub(crate) struct TableRule {
    pub(super) name: &'static str,
    pub(super) lhs: Term,
    pub(super) rhs: Term,
    /// the pattern variables of both sides are `V(0)..V(vars)`
    pub(super) vars: usize,
    pub(super) permutative: bool,
}

impl TableRule {
    pub(crate) fn new(name: &'static str, lhs: Term, rhs: Term) -> TableRule {
        let vars = lhs.max_var().max(rhs.max_var()) + 1;
        assert!(vars <= RULE_VARS, "{} -> {}: more than {RULE_VARS} pattern variables", lhs.show(), rhs.show());
        TableRule { name, lhs, rhs, vars, permutative: rule_permutative(&lhs, &rhs) }
    }
    fn is(&self, (l, r): &RuleKey) -> bool {
        self.lhs == *l && self.rhs == *r
    }
}

/// Pattern variables a rule may have (`rule_weight` counts them in arrays this long).
pub(super) const RULE_VARS: usize = 8;

/// A term's class as a rule pattern sees it: its operator, `0`, `-1` or a variable.
pub(super) const CLASSES: usize = OP_INFO.len() + 3;

pub(super) fn class(t: &Term) -> usize {
    match *t.node() {
        Node::Op(o, ..) => o,
        Node::Zero => OP_INFO.len(),
        Node::Ones => OP_INFO.len() + 1,
        Node::V(_) => OP_INFO.len() + 2,
    }
}

/// Patterns indexed by what they can match: for each class of term (`class`), the patterns in order whose root can match such
/// a term, each with the shape bits (`Term::needs`) that a match needs at each of the term's two operands, so the index
/// rules out a pattern down to its grandchildren (an operand's shape has its own class's bit, so its needs check its class
/// too), and the pairs of positions within depth 2 (`shallow`) where it has one subpattern (a repeated variable, say),
/// which a match must fill with one subterm, terms being hash-consed.
/// Keyed by the root operator alone, `rule_step_in` called `match_pat` on 16.7 rules a call, 31M a sweep
/// (docs/tier-cycle/, "Per-thread refills and the miner's trace matching"); with the operands' classes alone, 31% of the
/// join's matcher calls failed at the grandchildren and 8.5% at a leaf ("Why the join's matches fail"), and with the shape
/// alone, 48% on a repeated variable within depth 2 ("Which repeated-variable failures the index could reject"). The
/// join's index carries each step's `Need`, so a step over the cap is skipped without loading the step.
pub(super) struct PatIndex<K = ()> {
    by_class: [Vec<Entry<K>>; CLASSES],
}

/// A pattern's index, the shape bits it needs at the root's two operands (none for a leaf), the pairs of `shallow`
/// positions that must hold one subterm (bits of `PAIRS`), and what it carries.
type Entry<K> = (u32, [u64; 2], u16, K);

/// The positions within depth 2 of `t`'s root that `PatIndex` compares: its operands, then their operands (None where an
/// operand is a leaf, or for a leaf).
fn shallow(t: &Term) -> [Option<Term>; 6] {
    let Node::Op(_, a, b) = *t.node() else { return [None; 6] };
    let kids = |c: Term| match *c.node() {
        Node::Op(_, x, y) => [Some(x), Some(y)],
        _ => [None; 2],
    };
    let ([aa, ab], [ba, bb]) = (kids(a), kids(b));
    [Some(a), Some(b), aa, ab, ba, bb]
}

/// The pairs of `shallow` positions, one bit each.
const PAIRS: [(usize, usize); 15] = {
    let (mut p, mut i, mut k) = ([(0, 0); 15], 0, 0);
    while i < 6 {
        let mut j = i + 1;
        while j < 6 {
            p[k] = (i, j);
            (j, k) = (j + 1, k + 1);
        }
        i += 1;
    }
    p
};

impl<K: Copy> PatIndex<K> {
    /// Each pattern with what its entry carries (`K`), so a caller can drop it before looking the pattern up.
    pub(super) fn new<'a>(pats: impl Iterator<Item = (usize, &'a Term, K)>) -> PatIndex<K> {
        let mut ix = PatIndex { by_class: std::array::from_fn(|_| vec![]) };
        for (i, p, k) in pats {
            match *p.node() {
                Node::Op(_, a, b) => {
                    let at = shallow(p);
                    let same = |&(x, y): &(usize, usize)| matches!((at[x], at[y]), (Some(u), Some(v)) if u == v);
                    let pairs = PAIRS.iter().enumerate().filter(|(_, q)| same(q)).fold(0, |m, (b, _)| m | 1 << b);
                    ix.by_class[class(p)].push((i as u32, [a.needs(), b.needs()], pairs, k));
                }
                Node::V(_) => ix.by_class.iter_mut().for_each(|c| c.push((i as u32, [0; 2], 0, k))),
                Node::Zero | Node::Ones => ix.by_class[class(p)].push((i as u32, [0; 2], 0, k)),
            }
        }
        ix
    }

    /// The patterns that can match `t`, in order, each with its entry's `K`.
    pub(super) fn get(&self, t: &Term) -> impl Iterator<Item = (usize, K)> + '_ {
        let c = class(t);
        let [sa, sb] = match *t.node() {
            Node::Op(_, a, b) => [a.shape(), b.shape()],
            _ => [0; 2],
        };
        // whether some pair differs; a position the term lacks is a pattern's only where the shape rules the pattern out
        let at = shallow(t);
        let differ = move |mut pairs: u16| {
            let mut d = false;
            while pairs != 0 {
                let (x, y) = PAIRS[pairs.trailing_zeros() as usize];
                d |= at[x] != at[y];
                pairs &= pairs - 1;
            }
            d
        };
        // the shapes in one test without branches (an `all` over three shapes was 5.6% of the sweep's samples), the pairs
        // only for an entry that passes it (worked out for every subterm, they cost two thirds of what they saved)
        let fits = move |e: &&Entry<K>| (e.1[0] & !sa) | (e.1[1] & !sb) == 0 && (e.2 == 0 || !differ(e.2));
        self.by_class[c].iter().filter(fits).map(|&(i, _, _, k)| (i as usize, k))
    }
}

/// The rules `rule_step` tries, in order: the built-in ones, then the run-time ones (`mined`), indexed by their left sides
/// when not ablated; and the steps `join_eq` takes (`join_eqs`), indexed by the side each step rewrites.
pub struct RuleTable {
    pub mined: Vec<(Term, Term)>,
    pub(super) rules: Vec<TableRule>,
    index: PatIndex,
    pub(super) join: Vec<JoinEq>,
    pub(super) join_index: PatIndex<Need>,
    /// `join`'s steps by their law and direction (`lhs`, `rhs`, `backward`), the first of each, for `JoinStore`
    pub(super) join_key: hashbrown::HashMap<(Term, Term, bool), u32>,
}

impl RuleTable {
    /// `new` with `mined` in `run_order` (`Rules::new`).
    fn sorted(setup: &Setup, mut mined: Vec<(Term, Term)>) -> RuleTable {
        mined.sort_by_key(|(l, r)| run_order(l, r));
        RuleTable::new(setup, mined)
    }

    pub(super) fn new(setup: &Setup, mined: Vec<(Term, Term)>) -> RuleTable {
        let rules: Vec<TableRule> = setup.fixed_table().iter().copied().chain(mined.iter().map(|&(l, r)| TableRule::new("mined", l, r))).collect();
        let index = PatIndex::new(rules.iter().enumerate().filter(|(_, r)| !setup.ablated(r.name)).map(|(i, r)| (i, &r.lhs, ())));
        let join = join_eqs(setup, &rules);
        let join_index = PatIndex::new(join.iter().enumerate().map(|(i, e)| (i, &e.from, e.need)));
        let mut join_key = hashbrown::HashMap::new();
        for (i, e) in join.iter().enumerate() {
            join_key.entry((e.lhs, e.rhs, e.backward)).or_insert(i as u32);
        }
        RuleTable { mined, rules, index, join, join_index, join_key }
    }

    /// The rules that can match `t`, in order.
    pub(super) fn candidates(&self, t: &Term) -> impl Iterator<Item = (usize, &TableRule)> {
        self.index.get(t).map(|(i, ())| (i, &self.rules[i]))
    }
}

/// The run-time rules' order key (`RuleTable::sorted`).
pub fn run_order(l: &Term, r: &Term) -> (std::cmp::Reverse<usize>, Term, Term) {
    (std::cmp::Reverse(l.size()), *l, *r)
}

/// The first rule that fired on a term `rule_step` was asked about (`RewriteState::trace`): none, a built-in rule (tried before every
/// run-time rule) or a run-time rule; or `Join`, a term the join examined (`join_eq`), where every rule that matches gives a step.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Fired {
    None,
    Fixed,
    Mined(Term, Term),
    Join,
}

impl Fired {
    /// A run-time rule added to the rules that made this trace comes first on the term, `before(r)` saying whether it comes
    /// before run-time rule `r` (`run_order`): it rewrites the term if it matches it.
    pub fn preempted_by(&self, before: impl Fn(&(Term, Term)) -> bool) -> bool {
        match self {
            Fired::None | Fired::Join => true,
            Fired::Fixed => false,
            Fired::Mined(l, r) => before(&(*l, *r)),
        }
    }
}

/// The rules that do not change during a run, in the order `rule_step` tries them: the built-ins, then the promoted rules;
/// the mined ones (`Rules`) come after them. `Setup::fixed_rules` keeps them per task.
pub fn build_fixed_rules() -> Vec<Rule> {
    let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
    let v = Term::v;
    let shl = |a: Term| Term::op(SHL1, a, Term::ZERO);
    let shr = |a: Term| Term::op(SHR1, a, Term::ZERO);
    let lt = |a: Term, b: Term| Term::op(LT, a, b);
    let mut all = vec![
        Rule { name: "shldist", lhs: shl(op(0, v(0), v(1))), rhs: op(0, shl(v(0)), shl(v(1))) },
        Rule { name: "shldistsub", lhs: shl(op(4, v(0), v(1))), rhs: op(4, shl(v(0)), shl(v(1))) },
        Rule { name: "shldistand", lhs: shl(op(1, v(0), v(1))), rhs: op(1, shl(v(0)), shl(v(1))) },
        Rule { name: "shldistor", lhs: shl(op(2, v(0), v(1))), rhs: op(2, shl(v(0)), shl(v(1))) },
        Rule { name: "shldistxor", lhs: shl(op(3, v(0), v(1))), rhs: op(3, shl(v(0)), shl(v(1))) },
        Rule { name: "notsub", lhs: op(3, v(0), Term::ONES), rhs: op(4, Term::ONES, v(0)) },
        Rule { name: "notsubl", lhs: op(3, Term::ONES, v(0)), rhs: op(4, Term::ONES, v(0)) },
        // lt is false when the right side is 0, the left side is -1, or the sides are equal (mined, section 43)
        Rule { name: "ltself", lhs: lt(v(0), v(0)), rhs: lt(Term::ONES, Term::ONES) },
        Rule { name: "ltzero", lhs: lt(v(0), Term::ZERO), rhs: lt(Term::ONES, Term::ONES) },
        Rule { name: "ltmax", lhs: lt(Term::ONES, v(0)), rhs: lt(Term::ONES, Term::ONES) },
        Rule { name: "shrzero", lhs: shr(Term::ZERO), rhs: Term::ZERO },
        Rule { name: "shrdistand", lhs: shr(op(1, v(0), v(1))), rhs: op(1, shr(v(0)), shr(v(1))) },
        Rule { name: "shrdistor", lhs: shr(op(2, v(0), v(1))), rhs: op(2, shr(v(0)), shr(v(1))) },
        Rule { name: "shrdistxor", lhs: shr(op(3, v(0), v(1))), rhs: op(3, shr(v(0)), shr(v(1))) },
        Rule { name: "shrnot", lhs: shrnot_rule().0, rhs: shrnot_rule().1 },
        Rule { name: "shlzero", lhs: shl(Term::ZERO), rhs: Term::ZERO },
        Rule { name: "double", lhs: op(0, v(0), v(0)), rhs: shl(v(0)) },
        Rule { name: "doublechain", lhs: op(0, v(0), op(0, v(0), v(1))), rhs: op(0, shl(v(0)), v(1)) },
        // mined by `rule_miner` (section 36): cancellation
        Rule { name: "cancelr", lhs: op(4, op(0, v(0), v(1)), v(1)), rhs: v(0) },
        Rule { name: "cancell", lhs: op(4, op(0, v(0), v(1)), v(0)), rhs: v(1) },
        Rule { name: "subdist", lhs: op(4, op(0, v(0), v(1)), op(0, v(2), v(3))), rhs: op(0, op(4, v(0), v(2)), op(4, v(1), v(3))) },
    ];
    all.extend(promoted_rules().iter().map(|(l, r)| Rule { name: "promoted", lhs: *l, rhs: *r }));
    all
}

/// Rules chosen by `rule_miner` (search note section 60), promoted into the library as `lhs -> rhs` in `Term::show` syntax.
/// `ABLATE=promoted` removes them all; `promoted_rules_are_ordered_and_provable` checks order and proof.
pub const PROMOTED: &[(&str, &str)] = &[
    ("sub(shl1(x, 0), x)", "x"),
    ("sub(add(shl1(x, 0), y), x)", "add(x, y)"),
    ("sub(shl1(shl1(x, 0), 0), x)", "add(add(x, x), x)"),
    ("sub(x, 0)", "x"),
    ("sub(x, shl1(x, 0))", "sub(0, x)"),
    ("xor(shl1(-1, 0), shl1(shl1(-1, 0), 0))", "shl1(sub(0, -1), 0)"),
    ("sub(shl1(shl1(-1, 0), 0), -1)", "add(-1, add(-1, -1))"),
    ("lt(sub(x, y), x)", "lt(add(-1, y), x)"),
    ("lt(0, xor(x, -1))", "lt(x, -1)"),
    ("lt(xor(x, -1), -1)", "lt(0, x)"),
    ("lt(add(x, y), x)", "lt(sub(-1, x), y)"),
    ("lt(add(x, y), y)", "lt(sub(-1, x), y)"),
    ("lt(xor(x, -1), sub(y, x))", "lt(y, x)"),
    ("lt(xor(x, -1), xor(y, -1))", "lt(y, x)"),
    ("lt(0, sub(x, -1))", "lt(x, -1)"),
    ("lt(xor(x, -1), add(-1, x))", "lt(sub(0, x), x)"),
    ("lt(shl1(x, 0), -1)", "lt(0, -1)"),
    ("lt(xor(x, -1), shl1(-1, 0))", "lt(sub(0, -1), x)"),
    ("lt(x, add(-1, x))", "lt(x, sub(0, -1))"),
    ("lt(x, add(x, y))", "lt(x, sub(0, y))"),
    // from the shr family, second round (section 60)
    ("sub(x, sub(0, y))", "add(x, y)"),
    ("sub(x, add(x, y))", "sub(0, y)"),
    ("sub(sub(x, y), x)", "sub(0, y)"),
    ("add(sub(0, x), y)", "sub(y, x)"),
    ("sub(0, xor(x, -1))", "sub(x, -1)"),
    ("add(sub(x, y), x)", "sub(shl1(x, 0), y)"),
    ("sub(xor(x, -1), x)", "sub(-1, shl1(x, 0))"),
    ("sub(sub(x, -1), -1)", "sub(x, shl1(-1, 0))"),
    ("sub(x, add(y, x))", "sub(0, y)"),
    ("add(-1, xor(x, -1))", "sub(shl1(-1, 0), x)"),
    ("sub(xor(x, -1), -1)", "sub(0, x)"),
    ("sub(or(x, y), x)", "and(sub(-1, x), y)"),
    ("sub(or(x, y), y)", "and(sub(-1, y), x)"),
    ("sub(sub(0, x), x)", "sub(0, shl1(x, 0))"),
    ("sub(-1, sub(x, -1))", "sub(shl1(-1, 0), x)"),
];

/// The rules of a rule file: one `lhs -> rhs` per line, repeats once, other lines ignored.
pub fn parse_rules(text: &str) -> Vec<(Term, Term)> {
    let mut seen = hashbrown::HashSet::new();
    text.lines().filter_map(|l| l.split_once(" -> ")).map(|(a, b)| (parse_term(a), parse_term(b))).filter(|r| seen.insert(*r)).collect()
}

/// A `Term` from its `show` syntax: `0`, `-1`, a variable name, or `op(a, b)`.
pub fn parse_term(s: &str) -> Term {
    fn go(s: &[u8], i: &mut usize) -> Term {
        let start = *i;
        while *i < s.len() && !matches!(s[*i], b'(' | b',' | b')' | b' ') {
            *i += 1;
        }
        let name = std::str::from_utf8(&s[start..*i]).unwrap();
        if *i < s.len() && s[*i] == b'(' {
            let o = OP_INFO.iter().position(|o| o.name == name).unwrap_or_else(|| panic!("unknown op {name}"));
            *i += 1;
            let a = go(s, i);
            assert_eq!(&s[*i..*i + 2], b", ");
            *i += 2;
            let b = go(s, i);
            assert_eq!(s[*i], b')');
            *i += 1;
            return Term::op(o, a, b);
        }
        match name {
            "0" => Term::ZERO,
            "-1" => Term::ONES,
            _ => Term::v(VARS.iter().position(|v| *v == name).unwrap_or_else(|| panic!("unknown leaf {name}"))),
        }
    }
    let mut i = 0;
    let t = go(s.as_bytes(), &mut i);
    assert_eq!(i, s.len(), "trailing input in {s}");
    t
}

pub fn promoted_rules() -> &'static Vec<(Term, Term)> {
    static CACHE: std::sync::OnceLock<Vec<(Term, Term)>> = std::sync::OnceLock::new();
    CACHE.get_or_init(|| PROMOTED.iter().map(|(l, r)| (parse_term(l), parse_term(r))).collect())
}

/// First-order match of the pattern `p` against `t`, binding pattern variables in `sub` (a repeated variable must see equal terms).
impl Term {
    /// Occurrences of each variable (`out[v]`).
    pub fn occurrences(&self, out: &mut [usize; 8]) {
        match *self.node() {
            Node::V(v) => out[v] += 1,
            Node::Op(_, a, b) => {
                a.occurrences(out);
                b.occurrences(out);
            }
            _ => {}
        }
    }
    /// All subterms (with repeats), the term itself first.
    pub fn subterms(&self, out: &mut Vec<Term>) {
        out.push(*self);
        if let Node::Op(_, a, b) = *self.node() {
            a.subterms(out);
            b.subterms(out);
        }
    }
}

/// `shr1(sub(-1, x)) -> xor(shr1(x), shr1(-1))`: a shift of a bitwise not (`sub(-1, x)` is what `notsub` makes of
/// `xor(x, -1)`) distributes like the other bitwise operators; without it the not blocks `shrdistxor`.
pub fn shrnot_rule() -> (Term, Term) {
    let b = |o: usize, x: Term, y: Term| Term::op(o, x, y);
    let shr = |x: Term| b(SHR1, x, Term::ZERO);
    (shr(b(SUB, Term::ONES, Term::v(0))), b(XOR, shr(Term::v(0)), shr(Term::ONES)))
}

/// Proof of the `shrnot` rule through the middle term `shr1(xor(x, -1))`: the rewriter proves it equal to the left side
/// (with `notsub` on) and to the right side (with `notsub` off, so `shrdistxor` sees the xor), neither using `shrnot`.
pub fn shr_not_law(job: &mut Job, n: usize) -> Option<(Expr, Expr)> {
    let b = |o: usize, x: Term, y: Term| Term::op(o, x, y);
    let (l, r) = shrnot_rule();
    let m = b(SHR1, b(XOR, Term::v(0), Term::ONES), Term::ZERO);
    let own = (l, r);
    let notsub = job.setup().fixed_rules().iter().find(|x| x.name == "notsub").map(|x| (x.lhs, x.rhs))?;
    let prove = |job: &mut Job, blocked: &[RuleKey], t1: &Term, t2: &Term| proving(job, blocked, |job| rewrite_law(job, n, 1, t1, t2));
    let to_left = prove(job, std::slice::from_ref(&own), &m, &l)?;
    let to_right = prove(job, &[own, notsub], &m, &r)?;
    let (ops, bv) = (ops_for(n), bv_ty(n));
    let vals = vec![var(1)];
    let ev = |t: &Term| t.eval(&ops, n, &vals);
    let args = vec![var(1), var(0)];
    let (p1, p2) = (apps(to_left.0, args.clone()), apps(to_right.0, args));
    let body = trans_proof(&bv, &ev(&l), &ev(&m), &ev(&r), sym(&bv, &ev(&m), &ev(&l), p1), p2);
    let g = app(good_bv(n), var(0));
    let stmt = pi(g, id(bv, ev(&l), ev(&r)));
    Some((lam(bv, lam(g, body)), pi(bv, stmt)))
}

/// The law behind a rule: bitwise/shift rules by the per-position prover, the rest by the carry machines.
/// The most input bits (`n * k`) an every-input proof takes on: at 12, 4096 cases a position, about 0.4 s a rule to build
/// and check, and 16x that for each 4 bits more (docs/tier-cycle/, "At the loops' width, every-input proofs").
pub const EVERY_INPUT_BITS: usize = 12;

/// Proof of `t1 = t2` over `k` vectors at width `n` for any operators, by every input: per output position (`n`, or one
/// for a root `lt`), a case split over all `n * k` input bits whose leaves the kernel checks by evaluation (a Bool claim:
/// the split's motive is Type1, and a vector equality is Type2), then `cong_n` joins the positions.
pub fn every_input_law(n: usize, k: usize, t1: &Term, t2: &Term) -> (Expr, Expr) {
    let m = if matches!(*t1.node(), Node::Op(LT, ..)) { 1 } else { n };
    let ops = ops_for(n);
    let sides = |args: &[Expr]| (t1.eval(&ops, n, args), t2.eval(&ops, n, args));
    let tuples = |vs: &[Expr]| (0..k).map(|v| church_tuple(&vs[v * n..(v + 1) * n])).collect::<Vec<_>>();
    // bit `i` of a vector: the vector applied to Bool and the `i`th projection
    let proj = |v: Expr, i: usize| {
        let mut f = var((m - 1 - i) as u32);
        for _ in 0..m {
            f = lam(bool0(), f);
        }
        app2(v, bool0(), f)
    };
    let lemmas: Vec<Expr> = (0..m)
        .map(|i| {
            let body = |vs: &[Expr]| {
                let (l, r) = sides(&tuples(vs));
                id(bool0(), proj(l, i), proj(r, i))
            };
            lemma_n(n * k, &body, &|bits| refl(proj(sides(&tuples(&bits.iter().map(|b| bit(*b)).collect::<Vec<_>>())).0, i))).0
        })
        .collect();
    k_var_law_to(n, k, &bv_ty(m), &sides, &|bits, goods| {
        let at: Vec<(usize, usize)> = (0..k).flat_map(|v| (0..n).map(move |i| (v, i))).collect();
        let vs: Vec<Expr> = at.iter().map(|&(v, i)| bits(v, i)).collect();
        let args: Vec<Expr> = vs.iter().cloned().chain(at.iter().map(|&(v, i)| goods(v, i))).collect();
        let (l, r) = sides(&tuples(&vs));
        let (s1, s2): (Vec<Expr>, Vec<Expr>) = (0..m).map(|i| (proj(l, i), proj(r, i))).unzip();
        cong_n(&bool0(), &bv_ty(m), &bits_to_bv(m), &s1, &s2, lemmas.iter().map(|lm| apps(*lm, args.clone())).collect())
    })
}

/// Proof of the rule `l -> r` over `k` variables at width `n`: by its own route (the bitwise case split, `shr1` roots by
/// rewriting, the carry encoding), and past them over every input, up to `EVERY_INPUT_BITS` input bits.
pub fn prove_rule(job: &mut Job, n: usize, k: usize, l: &Term, r: &Term) -> Option<(Expr, Expr)> {
    routed_rule(job, n, k, l, r).or_else(|| {
        let law = (n * k <= EVERY_INPUT_BITS).then(|| every_input_law(n, k, l, r))?;
        job.lemmas.holds(&law.0, &law.1).ok().map(|_| law)
    })
}

fn routed_rule(job: &mut Job, n: usize, k: usize, l: &Term, r: &Term) -> Option<(Expr, Expr)> {
    if (l, r) == (&shrnot_rule().0, &shrnot_rule().1) {
        shr_not_law(job, n)
    } else if l.add_free() && r.add_free() {
        let law = bitwise_law_k(n, k, l, r);
        job.lemmas.holds(&law.0, &law.1).ok().map(|_| law)
    } else if matches!(*l.node(), Node::Op(SHR1, ..)) && matches!(*r.node(), Node::Op(SHR1, ..) | Node::Zero) || matches!(*r.node(), Node::Op(SHR1, ..)) && matches!(*l.node(), Node::Zero) {
        // laws with a `shr1` root are not machines: prove them with the rewriter (which falls back on the bit-0 mask
        // reduction), without the rule being proved, so that it cannot be used in its own proof
        proving(job, &[(*l, *r)], |job| rewrite_law(job, n, k, l, r))
    } else {
        add_tree_law(job, n, k, l, r)
    }
}

/// `f` (a proof of a rule by rewriting, with the rules `blocked`) run as a rewriting job of its own: a fresh
/// `RewriteState` with its own cycle path and a 10 000-step budget, no memo (the job's holds results under all the rules),
/// no trace, its own `rewrote`, and its machine fallbacks not counted for the caller, whose rewriting it does not change.
pub(super) fn proving<T>(job: &mut Job, blocked: &[RuleKey], f: impl FnOnce(&mut Job) -> T) -> T {
    let outer = job.blocked.len();
    job.blocked.extend(blocked.iter().cloned());
    let caller = std::mem::replace(&mut job.rw, RewriteState { budget: 10_000, ..Default::default() });
    let out = f(job);
    job.blocked.truncate(outer);
    job.rw = caller;
    out
}

/// The rule order's weight of a term, a polynomial interpretation `c + sum_v a_v * x_v` (`x_v >= 1` is the weight of
/// whatever replaces variable `v`): leaves 1, `shl1`/`shr1` double (`2x`, so distributing a shift over an operator goes
/// down), every other operator `x + y + 1`.
pub fn rule_weight(t: &Term) -> (i64, [i64; 8]) {
    match *t.node() {
        Node::V(v) => {
            let mut a = [0; 8];
            a[v] = 1;
            (0, a)
        }
        Node::Zero | Node::Ones => (1, [0; 8]),
        Node::Op(SHL1 | SHR1, x, _) => {
            let (c, mut a) = rule_weight(&x);
            a.iter_mut().for_each(|k| *k *= 2);
            (2 * c, a)
        }
        Node::Op(_, x, y) => {
            let ((c1, a1), (c2, a2)) = (rule_weight(&x), rule_weight(&y));
            (c1 + c2 + 1, std::array::from_fn(|v| a1[v] + a2[v]))
        }
    }
}

/// Whether `l -> r` goes down in the rule order: `l` outweighs `r` for every substitution (each variable's coefficient
/// no smaller, and the weight at all variables = 1 larger by at least 1), or ties there and `r` has fewer variable
/// occurrences (a tie-break, not a termination proof: `RewriteState::budget` backs it up, and `rule_step` skips a rewrite that
/// returns the same term).
pub fn rule_order_ok(l: &Term, r: &Term) -> bool {
    let ((cl, al), (cr, ar)) = (rule_weight(l), rule_weight(r));
    if (0..8).any(|v| ar[v] > al[v]) {
        return false;
    }
    let diff = cl - cr + (0..8).map(|v| al[v] - ar[v]).sum::<i64>();
    let (mut lo, mut ro) = ([0usize; 8], [0usize; 8]);
    l.occurrences(&mut lo);
    r.occurrences(&mut ro);
    diff >= 1 || (diff == 0 && ro.iter().sum::<usize>() < lo.iter().sum::<usize>())
}

/// The tie-break of the rule order (search note section 70), for patterns of equal weight and equal variable counts: `l`
/// above `r` by head precedence, else, for equal heads, at the first differing operand pair (left to right) by size and
/// then recursively. It orients reassociation rules (`sub(sub(x, y), z) -> sub(x, add(y, z))`) and `add`/`sub`
/// exchanges, not commutativity (`add(x, y) -> add(y, x)` has variables at the differing pair).
pub fn tie_greater(l: &Term, r: &Term) -> bool {
    match (*l.node(), *r.node()) {
        (Node::Op(lo, la, lb), Node::Op(ro, ra, rb)) => {
            if lo != ro {
                return OP_INFO[lo].prec > OP_INFO[ro].prec;
            }
            for (a, b) in [(la, ra), (lb, rb)] {
                if a != b {
                    return a.size() > b.size() || (a.size() == b.size() && tie_greater(&a, &b));
                }
            }
            false
        }
        (Node::Op(..), _) => true,
        _ => false,
    }
}

/// Whether `l` and `r` tie in the rule order: same weight and same variable occurrences.
pub fn rule_tied(l: &Term, r: &Term) -> bool {
    let ((cl, al), (cr, ar)) = (rule_weight(l), rule_weight(r));
    let (mut lo, mut ro) = ([0usize; 8], [0usize; 8]);
    l.occurrences(&mut lo);
    r.occurrences(&mut ro);
    cl == cr && al == ar && lo.iter().sum::<usize>() == ro.iter().sum::<usize>()
}

/// A permutative rule: tied in the rule order and not oriented by `tie_greater` either way (`add(sub(x, y), z) ->
/// add(sub(z, y), x)`). `rule_step` applies it only when the instance's right side is smaller than its left side by
/// `show()`, a total order on the instances (ordered rewriting), so it cannot undo itself.
pub fn rule_permutative(l: &Term, r: &Term) -> bool {
    !rule_order_ok(l, r) && rule_tied(l, r) && !tie_greater(l, r) && !tie_greater(r, l)
}

/// `rule_order_ok`, or a tie in it broken by `tie_greater`, or a permutative rule.
pub fn rule_order_or_tie(l: &Term, r: &Term) -> bool {
    rule_order_ok(l, r) || (rule_tied(l, r) && (tie_greater(l, r) || rule_permutative(l, r)))
}

/// Whether rule pattern `p` matches `t`, bindings on the stack: the rule miner asks this tens of millions of times a sweep
/// (docs/tier-cycle/, "Per-thread refills and the miner's trace matching").
pub fn matches(p: &Term, t: &Term) -> bool {
    match_pat(p, t, &mut [None; RULE_VARS])
}

pub fn match_pat(p: &Term, t: &Term, sub: &mut [Option<Term>]) -> bool {
    let mut nodes = 0;
    let m = match_in(p, t, sub, &mut nodes);
    crate::work::count_n(crate::work::Site::Match, nodes);
    m
}

/// `match_pat`, adding the pattern nodes it visits to `nodes`.
fn match_in(p: &Term, t: &Term, sub: &mut [Option<Term>], nodes: &mut u64) -> bool {
    *nodes += 1;
    match (*p.node(), *t.node()) {
        (Node::V(i), _) => match &sub[i] {
            Some(b) => b == t,
            None => {
                sub[i] = Some(*t);
                true
            }
        },
        (Node::Zero, Node::Zero) | (Node::Ones, Node::Ones) => true,
        (Node::Op(o, a, b), Node::Op(o2, c, d)) => o == o2 && match_in(&a, &c, sub, nodes) && match_in(&b, &d, sub, nodes),
        _ => false,
    }
}

/// Syntactic unification of `a` and `b` (variables shared, bindings in `sub`), with the occurs check.
pub fn unify(a: &Term, b: &Term, sub: &mut Vec<Option<Term>>) -> bool {
    fn resolve(t: &Term, sub: &[Option<Term>]) -> Term {
        match *t.node() {
            Node::V(i) => sub[i].as_ref().map_or_else(|| *t, |b| resolve(b, sub)),
            _ => *t,
        }
    }
    fn occurs(i: usize, t: &Term, sub: &[Option<Term>]) -> bool {
        match *resolve(t, sub).node() {
            Node::V(j) => i == j,
            Node::Op(_, x, y) => occurs(i, &x, sub) || occurs(i, &y, sub),
            _ => false,
        }
    }
    let (ra, rb) = (resolve(a, sub), resolve(b, sub));
    match (*ra.node(), *rb.node()) {
        (Node::V(i), Node::V(j)) if i == j => true,
        (Node::V(i), _) | (_, Node::V(i)) => {
            let t = if matches!(*ra.node(), Node::V(_)) { rb } else { ra };
            if occurs(i, &t, sub) {
                return false;
            }
            sub[i] = Some(t);
            true
        }
        (Node::Zero, Node::Zero) | (Node::Ones, Node::Ones) => true,
        (Node::Op(o, x1, y1), Node::Op(o2, x2, y2)) => o == o2 && unify(&x1, &x2, sub) && unify(&y1, &y2, sub),
        _ => false,
    }
}

/// The overlaps among `rules`: (i, j, at root) for each rule j whose left side unifies with a non-variable subterm of rule i's left
/// side (variables renamed apart; a rule with itself only below the root). Where two left sides overlap, first-match order decides
/// which rule rewrites, so these are the pairs a rule order (or completion) has to settle.
pub fn rule_overlaps(rules: &[(Term, Term)]) -> Vec<(usize, usize, bool)> {
    fn shift(t: &Term, k: usize) -> Term {
        match *t.node() {
            Node::V(i) => Term::v(i + k),
            Node::Op(o, a, b) => Term::op(o, shift(&a, k), shift(&b, k)),
            _ => *t,
        }
    }
    fn subterms<'a>(t: &'a Term, root: bool, out: &mut Vec<(&'a Term, bool)>) {
        if let Node::Op(_, a, b) = t.node() {
            out.push((t, root));
            subterms(a, false, out);
            subterms(b, false, out);
        }
    }
    let mut found = vec![];
    for (i, (li, _)) in rules.iter().enumerate() {
        let mut subs = vec![];
        subterms(li, true, &mut subs);
        for (j, (lj, _)) in rules.iter().enumerate() {
            let k = li.max_var() + 1;
            let lj = shift(lj, k);
            if let Some(&(_, root)) = subs.iter().find(|(s, root)| !(i == j && *root) && unify(s, &lj, &mut vec![None; k + lj.max_var() + 1])) {
                found.push((i, j, root));
            }
        }
    }
    found
}

pub fn subst_pat(p: &Term, sub: &[Option<Term>]) -> Term {
    match *p.node() {
        Node::V(i) => sub[i].expect("bound"),
        Node::Op(o, a, b) => Term::op(o, subst_pat(&a, sub), subst_pat(&b, sub)),
        _ => *p,
    }
}

/// The first library rule (not ablated) whose left side matches `t`: the rewritten term and the plan.
pub fn rule_step(job: &mut Job, t: &Term) -> Option<(Term, PlanRc)> {
    let rules = job.rules().clone();
    let table = &*rules.table;
    let all = &table.rules;
    let fires = |r: &TableRule| -> Option<[Option<Term>; RULE_VARS]> {
        let mut sub = [None; RULE_VARS];
        if !match_pat(&r.lhs, t, &mut sub) {
            return None;
        }
        if job.blocked.iter().any(|k| r.is(k)) {
            return None;
        }
        // a rule whose right side is an instance of its own left side (`lt(x,x) -> lt(-1,-1)`) must not rewrite its result
        let inst = subst_pat(&r.rhs, &sub.map(|s| s.or(Some(Term::ZERO))));
        if inst == *t {
            return None;
        }
        // a permutative rule (ordered rewriting): only when the instance goes down in the term order (that of the `show()` text)
        // (a path order on every tied instance, the removed `PERM_ORDER=lpo`, raised M, and the tie-break order before `show()`,
        // `PERM_ORDER=tie`, never became the default; the rewrite cycles both targeted are cut in `rewrite` instead: docs/tier-cycle/, "Cycle cut; lpo and a cycling penalty are negative results")
        if r.permutative && inst >= *t {
            return None;
        }
        Some(sub)
    };
    let first = table.candidates(t).find_map(|(i, r)| fires(r).map(|s| (i, s)));
    if let Some(v) = job.rw.trace.as_mut() {
        v.push((
            *t,
            match first {
                None => Fired::None,
                Some((i, _)) if all[i].name == "mined" => Fired::Mined(all[i].lhs, all[i].rhs),
                Some(_) => Fired::Fixed,
            },
        ));
    }
    let (i, sub) = first?;
    let r = &all[i];
    if rules.trace_rules {
        println!("TRACE {} -> {}   on {}", r.lhs.show(), r.rhs.show(), t.show());
    }
    job.rw.budget -= 1;
    if job.rw.budget < 0 {
        return None;
    }
    // a pattern variable the left side does not mention is free in the law: any value serves
    let args = sub[..r.vars].iter().map(|s| s.unwrap_or(Term::v(0))).collect();
    Some((subst_pat(&r.rhs, &sub), Plan::law(job, LawKind::Rule(r.name), r.lhs, r.rhs, args)))
}

/// The terms `rule_step` was asked about while rewriting, with the rule that fired on each (`RewriteState::trace`), and the OR of the
/// terms' shapes (`Term::shape`): a left side whose `needs` the OR lacks matches none of them, so most scans are skipped
/// without touching the terms (docs/tier-cycle/, "Survey: the next lever").
#[derive(Clone, Default)]
pub struct Trace {
    pub(super) items: Vec<(Term, Fired)>,
    pub(super) shapes: u64,
}

