use super::*;

// ---- Rewriting with proven lemmas (search note section 10). An `add` conjecture is simplified on both sides by
// the library lemmas `add a 0 = a`, `add 0 a = a` and `add a b = add b a` (the last used to order the operands),
// each rewrite justified by `cong_n` on the enclosing operator and chained with `trans_proof`; if the two
// results are then equal, or both add-free, `bitwise_law` closes the gap.

thread_local! {
    pub static CLOSED: std::cell::RefCell<hashbrown::HashMap<String, (tatic_kernel::PExpr, tatic_kernel::PExpr)>> = Default::default();
}
/// A closed library term built once per key (the proofs and witnesses the rewriter reuses at every step).
pub fn memo(key: String, build: impl FnOnce() -> (Expr, Expr)) -> (Expr, Expr) {
    if let Some(v) = CLOSED.with(|c| c.borrow().get(&key).map(|(p, s)| (p.get(), s.get()))) {
        return v;
    }
    let (p, s) = build();
    CLOSED.with(|c| c.borrow_mut().insert(key, (tatic_kernel::persist(p), tatic_kernel::persist(s))));
    (p, s)
}

/// A closed lemma `(proof, statement)` built once per key in the job: the proof is checked once (`Lemmas::ck`, against the
/// lemmas bound before it) and the lemma is returned as a parameter of that statement, so a law using it is checked
/// against the parameter, not the proof. `discharge` turns a term over parameters back into a closed one. A statement an
/// earlier process of the loop checked is bound without building its proof (`lemma_cache`).
pub fn shared_lemma(job: &mut Job, key: String, build: impl FnOnce(&mut Job) -> (Expr, Expr)) -> (Expr, Expr) {
    if let Some(v) = job.lemmas.bound.get(&key).map(|(r, s)| (r.get(), s.get())) {
        return v;
    }
    let setup = job.setup().clone();
    let (p, s) = match lemma_cache::lookup(&setup, &key) {
        Some(s) if !lemma_cache::recheck(&setup) => (None, s),
        cached => {
            let (p, s) = build(job);
            job.lemmas.ck(&format!("lemma {key}"), &p, &s);
            match cached {
                Some(c) => assert!(c == s, "LEMMA_RECHECK: the cached statement of {key} is not the one built"),
                None => lemma_cache::record(&setup, &key, &s),
            }
            (Some(p), s)
        }
    };
    let (ps, scopes) = job.lemmas.params.get_or_insert_with(|| (Postulates::new(), Vec::new()));
    let sc = ps.open();
    let r = ps.bind(s);
    scopes.push((sc, p.map(tatic_kernel::persist)));
    job.lemmas.bound.insert(key, (tatic_kernel::persist(r), tatic_kernel::persist(s)));
    (r, s)
}
/// `body` with the job's lemma parameters discharged, innermost first: `(\r_0. .. ((\r_m. body) P_m) ..) P_0`, a closed
/// term whose check re-checks every lemma proof `P_i` once. Ends the job's lemmas and everything that mentions them, so a
/// lemma asked for later is bound afresh.
pub fn discharge(job: &mut Job, body: Expr) -> Expr {
    let Some((mut ps, scopes)) = std::mem::take(&mut job.lemmas).params else { return body };
    scopes.into_iter().rev().fold(body, |b, (sc, p)| app(ps.close(sc, Binder::Lam, b), p.expect("discharge needs every lemma's proof: run without LEMMA_CACHE").get()))
}

/// `(value, GoodBv witness)` of `t` in context `[x, y, gx, gy]`.
pub fn witnessed(job: &mut Job, t: &Term, n: usize, goods: &[(Expr, Expr)]) -> (Expr, Expr) {
    let all = low_bits(n);
    match *t.node() {
        Node::V(i) => goods[i],
        Node::Zero => (lit(n, 0), good_lit(n, 0)),
        Node::Ones => (lit(n, all), good_lit(n, all)),
        Node::Op(o, a, b) => {
            let ((av, aw), (bv, bw)) = (witnessed(job, &a, n, goods), witnessed(job, &b, n, goods));
            let (op, good_op) = match o {
                0 => (add(n), shared_lemma(job, format!("good_add{n}"), |_| good_add(n)).0),
                4 => (sub(n), shared_lemma(job, format!("good_sub{n}"), |_| good_sub(n)).0),
                6 => (shl1_op(n), shared_lemma(job, format!("good_shl1{n}"), |_| good_shl1(n)).0),
                7 => (shr1_op(n), shared_lemma(job, format!("good_shr1{n}"), |_| good_shr1(n)).0),
                _ => memo(format!("gbit{n}_{o}"), || {
                    let opf = move |p: Expr, q: Expr| match o {
                        1 => and(p, q),
                        2 => or(p, q),
                        _ => xor(p, q),
                    };
                    let (g, _) = match o {
                        1 => good2(&|p, q| and(p, q), &OP_INFO[1].truth),
                        2 => good2(&|p, q| or(p, q), &OP_INFO[2].truth),
                        _ => good2(&|p, q| xor(p, q), &OP_INFO[3].truth),
                    };
                    let vec = bitwise(n, &opf);
                    let (gp, _) = good_vec(n, vec, &move |a, b, ga, gb| {
                        let s = (0..n).map(|i| opf(a[i], b[i])).collect();
                        let gs = (0..n).map(|i| apps(g, vec![a[i], b[i], ga[i], gb[i]])).collect();
                        (s, gs)
                    });
                    (vec, gp)
                }),
            };
            (app2(op, av, bv), apps(good_op, vec![av, bv, aw, bw]))
        }
    }
}

/// How a rewrite `lhs = rhs` is justified. The rewriter makes plans and builds no kernel terms; `Compiler` turns a plan into a
/// proof when one is wanted, so counting (`RULEMINER_FAST`) never builds one.
pub enum Plan {
    /// `t = t`
    Refl(Term),
    /// `o(a, b) = o(a', b')` from `a = a'` and `b = b'`
    Cong(usize, PlanRc, PlanRc),
    /// `a = c` from `a = b` and `b = c`
    Trans(PlanRc, PlanRc),
    /// `b = a` from `a = b`
    Sym(PlanRc),
    /// the closed law `lhs = rhs` over the pattern variables `V(0..)`, at the terms `args` (one per variable)
    Law(LawKind, Term, Term, Vec<Term>),
    /// any step taken while counting (`Rules::counting`), which compiles no plan: the constructors share one, so scoring allocates
    /// none (they were 1.6% of a sweep's samples; docs/tier-cycle/, "Survey: the lemmas and the allocator")
    Counting,
}
pub type PlanRc = std::rc::Rc<Plan>;

/// The prover of a `Plan::Law`.
#[derive(Clone, Copy)]
pub enum LawKind {
    /// a library rule, by name (`prove_rule`)
    Rule(&'static str),
    /// `(x + y) + z = x + (y + z)`
    Assoc,
    /// `x + y = y + x`
    Comm,
    /// `bitwise_law_k`
    Bitwise,
    /// `add_tree_law`
    Tree,
}

impl Plan {
    /// `make()`, or while counting the shared `Plan::Counting`.
    fn new(job: &Job, make: impl FnOnce() -> Plan) -> PlanRc {
        thread_local! {
            static COUNTING: PlanRc = PlanRc::new(Plan::Counting);
        }
        if job.rules().score_only { COUNTING.with(PlanRc::clone) } else { PlanRc::new(make()) }
    }
    pub fn refl(job: &Job, t: &Term) -> PlanRc {
        Plan::new(job, || Plan::Refl(*t))
    }
    pub fn cong(job: &Job, o: usize, a: PlanRc, b: PlanRc) -> PlanRc {
        Plan::new(job, || Plan::Cong(o, a, b))
    }
    pub fn trans(job: &Job, a: PlanRc, b: PlanRc) -> PlanRc {
        Plan::new(job, || Plan::Trans(a, b))
    }
    pub fn sym(job: &Job, a: PlanRc) -> PlanRc {
        Plan::new(job, || Plan::Sym(a))
    }
    pub fn law(job: &Job, kind: LawKind, lhs: Term, rhs: Term, args: Vec<Term>) -> PlanRc {
        Plan::new(job, || Plan::Law(kind, lhs, rhs, args))
    }
}

/// The variables `V(0..k)`: a law's arguments when it is stated over the conjecture's own variables.
pub(super) fn vars(k: usize) -> Vec<Term> {
    (0..k).map(Term::v).collect()
}

/// Compiles plans into kernel proofs at width `n`, in context `[x.., gx..]` over `k` good vectors.
pub struct Compiler {
    n: usize,
    ops: [Expr; 8],
    goods: Vec<(Expr, Expr)>,
    vals: Vec<Expr>,
}

impl Compiler {
    pub fn new(n: usize, k: usize) -> Compiler {
        let goods: Vec<(Expr, Expr)> = (0..k).map(|i| (var((2 * k - 1 - i) as u32), var((k - 1 - i) as u32))).collect();
        Compiler { n, ops: ops_for(n), vals: goods.iter().map(|g| g.0).collect(), goods }
    }

    pub fn ev(&self, t: &Term) -> Expr {
        t.eval(&self.ops, self.n, &self.vals)
    }

    /// The type of `t`'s value: one bit under an `lt` root, else `n` bits.
    fn ty(&self, t: &Term) -> Expr {
        bv_ty(if matches!(*t.node(), Node::Op(LT, ..)) { 1 } else { self.n })
    }

    /// The plan's two sides and the proof of `Id(lhs, rhs)`.
    pub fn proof(&self, job: &mut Job, plan: &Plan) -> (Term, Term, Expr) {
        let n = self.n;
        match plan {
            Plan::Counting => panic!("a plan made while counting has nothing to compile"),
            Plan::Refl(t) => (*t, *t, refl(self.ev(t))),
            Plan::Cong(o, a, b) => {
                let ((a1, a2, pa), (b1, b2, pb)) = (self.proof(job, a), self.proof(job, b));
                let (xs, ys) = ([self.ev(&a1), self.ev(&b1)], [self.ev(&a2), self.ev(&b2)]);
                let (l, r) = (Term::op(*o, a1, b1), Term::op(*o, a2, b2));
                let p = cong_n(&bv_ty(n), &self.ty(&l), &self.ops[*o], &xs, &ys, vec![pa, pb]);
                (l, r, p)
            }
            Plan::Trans(a, b) => {
                let ((x, y, p), (_, z, q)) = (self.proof(job, a), self.proof(job, b));
                let p = trans_proof(&self.ty(&x), &self.ev(&x), &self.ev(&y), &self.ev(&z), p, q);
                (x, z, p)
            }
            Plan::Sym(a) => {
                let (x, y, p) = self.proof(job, a);
                let p = sym(&self.ty(&x), &self.ev(&x), &self.ev(&y), p);
                (y, x, p)
            }
            Plan::Law(kind, l, r, args) => {
                let k = args.len();
                // Every law is checked once and used as a parameter of its statement (`shared_lemma`).
                let prover = match kind {
                    LawKind::Rule(name) => format!("rule_{name}"),
                    LawKind::Assoc => "assoc".into(),
                    LawKind::Comm => "comm".into(),
                    LawKind::Bitwise => "bitwise".into(),
                    LawKind::Tree => "tree".into(),
                };
                let law = shared_lemma(job, format!("{prover}_{}_{}_{n}_{k}", l.show(), r.show()), |job| match kind {
                    LawKind::Rule(name) => prove_rule(job, n, k, l, r).unwrap_or_else(|| panic!("rule {name} is not provable")),
                    LawKind::Assoc => add_assoc_proof(n, false),
                    LawKind::Comm => add_comm_proof(n, false),
                    LawKind::Bitwise => bitwise_law_k(n, k, l, r),
                    LawKind::Tree => add_tree_law(job, n, k, l, r).expect("a carry encoding"),
                })
                .0;
                let w: Vec<(Expr, Expr)> = args.iter().map(|t| witnessed(job, t, n, &self.goods)).collect();
                let p = apps(law, w.iter().map(|x| x.0).chain(w.iter().map(|x| x.1)).collect());
                let sub: Vec<Option<Term>> = args.iter().cloned().map(Some).collect();
                (subst_pat(l, &sub), subst_pat(r, &sub), p)
            }
        }
    }
}

/// A library law used as a left-to-right rewrite rule: `lhs = rhs` over the pattern variables `V(0)..`, each instance
/// proved from the law `add_tree_law` proves once (per width) for the patterns themselves. `name` is the `ABLATE` key.
pub struct Rule {
    pub name: &'static str,
    pub lhs: Term,
    pub rhs: Term,
}

