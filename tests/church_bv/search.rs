use super::*;

/// The binary gates of a diagram: 0 and, 1 or, 2 xor.
pub fn bop(op: usize, a: Expr, b: Expr) -> Expr {
    match op {
        0 => and(a, b),
        1 => or(a, b),
        _ => xor(a, b),
    }
}
pub fn bop_val(op: usize, a: bool, b: bool) -> bool {
    match op {
        0 => a && b,
        1 => a || b,
        _ => a != b,
    }
}
pub fn bop_fn(op: usize) -> Expr {
    match op {
        0 => and_(),
        1 => or_(),
        _ => xor_(),
    }
}

/// The closed lemmas the diagram's steps instantiate (each `Pi bits. GoodBool bits -> Id(Bool0, l, r)`), over bits in
/// the order given: `same[op]`: `op (mux v a b) (mux v c d) = mux v (op a c) (op b d)` (`v a b c d`); `skipl[op]`:
/// `op (mux v a b) y = mux v (op a y) (op b y)` (`v a b y`); `skipr[op]`: `op x (mux v c d) = mux v (op x c) (op x d)`
/// (`v x c d`); `red`: `mux v x x = x` (`v x`); `var`: `v = mux v true false` (`v`).
pub struct DdLemmas {
    pub same: Vec<Expr>,
    pub skipl: Vec<Expr>,
    pub skipr: Vec<Expr>,
    pub red: Expr,
    pub var: Expr,
}

thread_local! {
    pub static DD_LEMMAS: std::cell::RefCell<Option<std::rc::Rc<DdLemmas>>> = Default::default();
}

/// `Id(Bool0, lhs, rhs)` over `k` bits by case analysis (each leaf is `refl`, checked by evaluation).
pub fn eq_lemma(k: usize, lhs: &dyn Fn(&[Expr]) -> Expr, rhs: &dyn Fn(&[Expr]) -> Expr) -> Expr {
    lemma_n(k, &|v| id(bool0(), lhs(v), rhs(v)), &|bits| refl(lhs(&bits.iter().map(|b| bit(*b)).collect::<Vec<_>>()))).0
}

pub fn dd_lemmas() -> std::rc::Rc<DdLemmas> {
    if let Some(l) = DD_LEMMAS.with(|c| c.borrow().clone()) {
        return l;
    }
    let mut same = vec![];
    let mut skipl = vec![];
    let mut skipr = vec![];
    for op in 0..3 {
        same.push(eq_lemma(
            5,
            &move |v| bop(op, mux(v[0].clone(), v[1].clone(), v[2].clone()), mux(v[0].clone(), v[3].clone(), v[4].clone())),
            &move |v| mux(v[0].clone(), bop(op, v[1].clone(), v[3].clone()), bop(op, v[2].clone(), v[4].clone())),
        ));
        skipl.push(eq_lemma(
            4,
            &move |v| bop(op, mux(v[0].clone(), v[1].clone(), v[2].clone()), v[3].clone()),
            &move |v| mux(v[0].clone(), bop(op, v[1].clone(), v[3].clone()), bop(op, v[2].clone(), v[3].clone())),
        ));
        skipr.push(eq_lemma(
            4,
            &move |v| bop(op, v[1].clone(), mux(v[0].clone(), v[2].clone(), v[3].clone())),
            &move |v| mux(v[0].clone(), bop(op, v[1].clone(), v[2].clone()), bop(op, v[1].clone(), v[3].clone())),
        ));
    }
    let red = eq_lemma(2, &|v| mux(v[0].clone(), v[1].clone(), v[1].clone()), &|v| v[1].clone());
    let var = eq_lemma(1, &|v| v[0].clone(), &|v| mux(v[0].clone(), t(), f()));
    let l = std::rc::Rc::new(DdLemmas { same, skipl, skipr, red, var });
    DD_LEMMAS.with(|c| *c.borrow_mut() = Some(l.clone()));
    l
}

/// A Boolean expression `e`, its diagram node `n`, and `p : Id(Bool0, e, C(n))`.
#[derive(Clone)]
pub struct Sig {
    pub e: Expr,
    pub n: usize,
    pub p: Expr,
}

/// The diagram under construction for one lemma: bit variable `i` is `vars[i]` with witness `goods[i]`.
pub struct Dd {
    pub lem: std::rc::Rc<DdLemmas>,
    pub vars: Vec<Expr>,
    pub goods: Vec<Expr>,
    pub gops: GoodOps,
    /// `(variable, hi, lo)`, node id = index + 2 (0 is false, 1 is true).
    pub nodes: Vec<(usize, usize, usize)>,
    pub unique: std::collections::HashMap<(usize, usize, usize), usize>,
    pub canon: std::collections::HashMap<usize, (Expr, Expr)>,
    pub applied: std::collections::HashMap<(usize, usize, usize), (usize, Expr)>,
}

impl Dd {
    pub fn mk(&mut self, var: usize, hi: usize, lo: usize) -> usize {
        if hi == lo {
            return hi;
        }
        if let Some(n) = self.unique.get(&(var, hi, lo)) {
            return *n;
        }
        self.nodes.push((var, hi, lo));
        let n = self.nodes.len() + 1;
        self.unique.insert((var, hi, lo), n);
        n
    }
    pub fn var_of(&self, n: usize) -> usize {
        if n < 2 { usize::MAX } else { self.nodes[n - 2].0 }
    }
    /// The canonical term of node `n` and its `GoodBool` witness.
    pub fn canon(&mut self, n: usize) -> (Expr, Expr) {
        if n < 2 {
            return (bit(n == 1), good_bit(n == 1));
        }
        if let Some(c) = self.canon.get(&n) {
            return c.clone();
        }
        let (v, hi, lo) = self.nodes[n - 2];
        let (ch, gh) = self.canon(hi);
        let (cl, gl) = self.canon(lo);
        let c = Gb { e: self.vars[v].clone(), g: self.goods[v].clone() };
        let one = Gb { e: t(), g: good_bit(true) };
        let not_c = self.gops.xor(&c, &one);
        let a1 = self.gops.and(&c, &Gb { e: ch, g: gh });
        let a2 = self.gops.and(&not_c, &Gb { e: cl, g: gl });
        let r = self.gops.or(&a1, &a2);
        self.canon.insert(n, (r.e.clone(), r.g.clone()));
        (r.e, r.g)
    }
    /// The node of `op(a, b)` and a proof of `Id(Bool0, op(C(a), C(b)), C(node))`.
    pub fn apply(&mut self, op: usize, a: usize, b: usize) -> (usize, Expr) {
        if let Some(r) = self.applied.get(&(op, a, b)) {
            return r.clone();
        }
        let (ca, ga) = self.canon(a);
        let (cb, gb) = self.canon(b);
        let res = if a < 2 && b < 2 {
            (bop_val(op, a == 1, b == 1) as usize, refl(bop(op, ca, cb)))
        } else {
            let (va, vb) = (self.var_of(a), self.var_of(b));
            let m = va.min(vb);
            let (ah, al) = if va == m { (self.nodes[a - 2].1, self.nodes[a - 2].2) } else { (a, a) };
            let (bh, bl) = if vb == m { (self.nodes[b - 2].1, self.nodes[b - 2].2) } else { (b, b) };
            let (rh, ph) = self.apply(op, ah, bh);
            let (rl, pl) = self.apply(op, al, bl);
            let r = self.mk(m, rh, rl);
            let (v, gv) = (self.vars[m].clone(), self.goods[m].clone());
            let ((cah, gah), (cal, gal), (cbh, gbh), (cbl, gbl)) = (self.canon(ah), self.canon(al), self.canon(bh), self.canon(bl));
            let ((crh, grh), (crl, _)) = (self.canon(rh), self.canon(rl));
            let step1 = if va == m && vb == m {
                apps(self.lem.same[op].clone(), vec![v.clone(), cah.clone(), cal.clone(), cbh.clone(), cbl.clone(), gv.clone(), gah, gal, gbh, gbl])
            } else if va == m {
                apps(self.lem.skipl[op].clone(), vec![v.clone(), cah.clone(), cal.clone(), cb.clone(), gv.clone(), gah, gal, gb])
            } else {
                apps(self.lem.skipr[op].clone(), vec![v.clone(), ca.clone(), cbh.clone(), cbl.clone(), gv.clone(), ga, gbh, gbl])
            };
            let (xh, xl) = (bop(op, cah, cbh), bop(op, cal, cbl));
            let mid = mux(v.clone(), xh.clone(), xl.clone());
            let target = mux(v.clone(), crh.clone(), crl.clone());
            let fm = lam(bool0(), lam(bool0(), mux(shift(&v, 0, 2), var(1), var(0))));
            let step2 = cong_n(&bool0(), &bool0(), &fm, &[xh, xl], &[crh.clone(), crl.clone()], vec![ph, pl]);
            let lhs = bop(op, ca, cb);
            let p12 = trans_proof(&bool0(), &lhs, &mid, &target, step1, step2);
            if rh == rl {
                let red = apps(self.lem.red.clone(), vec![v, crh.clone(), gv, grh]);
                (r, trans_proof(&bool0(), &lhs, &target, &crh, p12, red))
            } else {
                (r, p12)
            }
        };
        self.applied.insert((op, a, b), res.clone());
        res
    }
}

/// The gate operations shared by the proof-term builder (`GoodOps`, over `Gb`) and the diagram (`DdGates`, over `Sig`).
pub trait Gates {
    type S: Clone;
    fn and(&self, x: &Self::S, y: &Self::S) -> Self::S;
    fn or(&self, x: &Self::S, y: &Self::S) -> Self::S;
    fn xor(&self, x: &Self::S, y: &Self::S) -> Self::S;
    fn konst(&self, b: bool) -> Self::S;
    /// The truth table `tab` over the signals `vars`.
    fn table(&self, vars: &[Self::S], tab: &dyn Fn(&[bool]) -> bool) -> Self::S;
    fn sum3(&self, a: &Self::S, b: &Self::S, c: &Self::S) -> Self::S {
        let ab = self.xor(a, b);
        self.xor(&ab, c)
    }
    fn maj(&self, a: &Self::S, b: &Self::S, c: &Self::S) -> Self::S {
        let (ab, x) = (self.and(a, b), self.xor(a, b));
        let cx = self.and(c, &x);
        self.or(&ab, &cx)
    }
}

impl Gates for GoodOps {
    type S = Gb;
    fn and(&self, x: &Gb, y: &Gb) -> Gb {
        GoodOps::and(self, x, y)
    }
    fn or(&self, x: &Gb, y: &Gb) -> Gb {
        GoodOps::or(self, x, y)
    }
    fn xor(&self, x: &Gb, y: &Gb) -> Gb {
        GoodOps::xor(self, x, y)
    }
    fn konst(&self, b: bool) -> Gb {
        Gb { e: bit(b), g: good_bit(b) }
    }
    /// The witness is a placeholder: claims built this way are only stated, never proved through it.
    fn table(&self, vars: &[Gb], tab: &dyn Fn(&[bool]) -> bool) -> Gb {
        Gb { e: table_app(&vars.iter().map(|g| g.e.clone()).collect::<Vec<_>>(), tab), g: f() }
    }
}

pub struct DdGates {
    pub dd: std::cell::RefCell<Dd>,
}

impl DdGates {
    pub fn new(vars: Vec<Expr>, goods: Vec<Expr>) -> DdGates {
        DdGates {
            dd: std::cell::RefCell::new(Dd {
                lem: dd_lemmas(),
                vars,
                goods,
                gops: GoodOps::new(),
                nodes: vec![],
                unique: Default::default(),
                canon: Default::default(),
                applied: Default::default(),
            }),
        }
    }
    pub fn var_sig(&self, i: usize) -> Sig {
        let mut dd = self.dd.borrow_mut();
        let n = dd.mk(i, 1, 0);
        let (v, gv) = (dd.vars[i].clone(), dd.goods[i].clone());
        Sig { e: v.clone(), n, p: apps(dd.lem.var.clone(), vec![v, gv]) }
    }
    pub fn gate(&self, op: usize, x: &Sig, y: &Sig) -> Sig {
        let mut dd = self.dd.borrow_mut();
        let (r, pr) = dd.apply(op, x.n, y.n);
        let (cx, cy, cr) = (dd.canon(x.n).0, dd.canon(y.n).0, dd.canon(r).0);
        let congp = cong_n(&bool0(), &bool0(), &bop_fn(op), &[x.e.clone(), y.e.clone()], &[cx.clone(), cy.clone()], vec![x.p.clone(), y.p.clone()]);
        let p = trans_proof(&bool0(), &bop(op, x.e.clone(), y.e.clone()), &bop(op, cx, cy), &cr, congp, pr);
        Sig { e: bop(op, x.e.clone(), y.e.clone()), n: r, p }
    }
    /// `Id(Bool0, a.e, b.e)` when both signals are the same function.
    pub fn equate(&self, a: &Sig, b: &Sig) -> Option<Expr> {
        if a.n != b.n {
            return None;
        }
        let c = self.dd.borrow_mut().canon(a.n).0;
        Some(trans_proof(&bool0(), &a.e, &c, &b.e, a.p.clone(), sym(&bool0(), &b.e, &c, b.p.clone())))
    }
}

impl Gates for DdGates {
    type S = Sig;
    fn and(&self, x: &Sig, y: &Sig) -> Sig {
        self.gate(0, x, y)
    }
    fn or(&self, x: &Sig, y: &Sig) -> Sig {
        self.gate(1, x, y)
    }
    fn xor(&self, x: &Sig, y: &Sig) -> Sig {
        self.gate(2, x, y)
    }
    fn konst(&self, b: bool) -> Sig {
        Sig { e: bit(b), n: b as usize, p: refl(bit(b)) }
    }
    /// The table's own reduced diagram, composed along its nodes (each node a `mux` of the signal at its level), so the
    /// expression is the body of `table_app` instantiated; `e` is stated in `table_app` form (the same term up to beta).
    fn table(&self, vars: &[Sig], tab: &dyn Fn(&[bool]) -> bool) -> Sig {
        let d = tab_bdd(vars.len(), tab);
        let one = self.konst(true);
        let mut sigs: Vec<Sig> = vec![self.konst(false), one.clone()];
        for &(level, hi, lo) in &d.nodes {
            let c = &vars[level];
            let not_c = self.xor(c, &one);
            let (a1, a2) = (self.and(c, &sigs[hi]), self.and(&not_c, &sigs[lo]));
            let s = self.or(&a1, &a2);
            sigs.push(s);
        }
        let mut s = sigs[d.root].clone();
        s.e = table_app(&vars.iter().map(|v| v.e.clone()).collect::<Vec<_>>(), tab);
        s
    }
}

/// Closed `Pi bits. GoodBool bits -> Id(Bool0, a, b)` for the two signals `build` makes from the bit variables, by
/// diagrams instead of a case tree; `None` when they are different functions. Same shape as `lemma_n`'s proof.
pub fn lemma_dd(nv: usize, build: DdBuild) -> Option<Expr> {
    let vars: Vec<Expr> = (0..nv).map(|m| var((2 * nv - 1 - m) as u32)).collect();
    let goods: Vec<Expr> = (0..nv).map(|m| var((nv - 1 - m) as u32)).collect();
    let g = DdGates::new(vars, goods);
    let inputs: Vec<Sig> = (0..nv).map(|i| g.var_sig(i)).collect();
    let (a, b) = build(&g, &inputs);
    let mut proof = g.equate(&a, &b)?;
    for _ in 0..nv {
        proof = lam(app(good_bool(), var(nv as u32 - 1)), proof);
    }
    for _ in 0..nv {
        proof = lam(bool0(), proof);
    }
    Some(proof)
}

#[test]
pub fn decision_diagram_proofs_check_and_beat_the_case_tree() {
    let _scope = tatic::kernel::InternScope::enter();
    // associativity of xor over 3 bits, against `lemma_n`'s statement
    let sides = |g: &DdGates, v: &[Sig]| (g.xor(&g.xor(&v[0], &v[1]), &v[2]), g.xor(&v[0], &g.xor(&v[1], &v[2])));
    let (pn, ty) = lemma_n(
        3,
        &|v| id(bool0(), xor(xor(v[0].clone(), v[1].clone()), v[2].clone()), xor(v[0].clone(), xor(v[1].clone(), v[2].clone()))),
        &|bits| {
            let l = |i: usize| bit(bits[i]);
            refl(xor(xor(l(0), l(1)), l(2)))
        },
    );
    ck("case tree", &pn, &ty);
    let pd = lemma_dd(3, &sides).expect("same function");
    ck("diagram", &pd, &ty);
    // a false equation has no diagram proof
    assert!(lemma_dd(2, &|g, v| (g.and(&v[0], &v[1]), g.or(&v[0], &v[1]))).is_none());
    // a chain of 14 bits in two association orders: 2^14 case-tree leaves, a few dozen diagram nodes
    let nv = 14;
    let chain = |g: &DdGates, v: &[Sig]| {
        let left = v[1..].iter().fold(v[0].clone(), |a, b| g.xor(&a, b));
        let right = v[..nv - 1].iter().rev().fold(v[nv - 1].clone(), |a, b| g.xor(b, &a));
        (left, right)
    };
    let t0 = Instant::now();
    let pd = lemma_dd(nv, &chain).expect("parity chains agree");
    let built = t0.elapsed();
    let vv = |m: usize| var((2 * nv - 1 - m) as u32);
    let left = (1..nv).fold(vv(0), |a, i| xor(a, vv(i)));
    let right = (0..nv - 1).rev().fold(vv(nv - 1), |a, i| xor(vv(i), a));
    let mut ty = id(bool0(), left, right);
    for _ in 0..nv {
        ty = pi(app(good_bool(), var(nv as u32 - 1)), ty);
    }
    for _ in 0..nv {
        ty = pi(bool0(), ty);
    }
    let t1 = Instant::now();
    ck("parity chains", &pd, &ty);
    println!("DD 14-bit parity chains: build {built:?}, check {:?}", t1.elapsed());
}

/// Rewriting with the library rules over every constant-multiplication law (search note section 35): per law the
/// carries of the target machines, whether a whole-term machine proof was still needed, build and check times; the
/// totals show what the rules buy. `ABLATE=shldist,shldistsub,double,doublechain` (any subset) removes rules.
#[test]
#[ignore]
pub fn rewrite_rules_over_the_mul_laws() {
    let _scope = tatic::kernel::InternScope::enter();
    println!("RULES machine at start: {}", machine_state());
    let max = env_or("MULMINER_MAX", 7);
    let (mut proved, mut none, mut machine_free, mut over_cap, t0) = (0, 0, 0, 0, Instant::now());
    for (name, t1, t2) in mul_laws(max) {
        if !(1..=6).all(|w| t1.plausibly_equals(&t2, w, 2)) {
            continue;
        }
        let cs = [&t1, &t2].map(|t| Machine::parse(t).map_or(0, |m| m.carries()));
        let before = MACHINE_FALLBACKS.with(|c| c.get());
        let t = Instant::now();
        let r = rewrite_law(4, 2, &t1, &t2);
        let built = t.elapsed();
        let fell = MACHINE_FALLBACKS.with(|c| c.get()) - before;
        match r {
            Some((p, s)) => {
                let t = Instant::now();
                ck(&name, &p, &s);
                proved += 1;
                machine_free += (fell == 0) as u32;
                over_cap += (cs[0].max(cs[1]) > carry_cap()) as u32;
                println!("RULES {name}: carries {cs:?}, machine proofs used {fell}, build {built:?}, check {:?}", t.elapsed());
            }
            None => {
                none += 1;
                println!("RULES {name}: carries {cs:?}, no proof, {built:?}");
            }
        }
    }
    println!("RULES machine at end: {}", machine_state());
    println!("RULES rule instances: {:?}", RULE_HITS.lock().unwrap());
    println!("RULES {proved} proved ({machine_free} with no whole-term machine proof, {over_cap} beyond the carry cap), {none} not, {:?}", t0.elapsed());
}

/// Rules from a file, one `lhs -> rhs` per line in `Term::show` syntax (blank lines and `#` comments skipped); the format of `RULEMINER_EXTRA`.
pub fn read_rule_file(path: &str) -> Vec<(Term, Term)> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let mut out = vec![];
    let mut seen = std::collections::HashSet::new();
    for line in text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
        let Some((l, r)) = line.split_once(" -> ") else {
            println!("RULEMINER extra file: skipped (no ' -> '): {line}");
            continue;
        };
        let parsed = std::panic::catch_unwind(|| (parse_term(l.trim()), parse_term(r.trim())));
        match parsed {
            Ok((l, r)) if matches!(l, Term::Op(..)) && l.show() != r.show() && seen.insert(format!("{} => {}", l.show(), r.show())) => out.push((l, r)),
            Ok(_) => {}
            Err(_) => println!("RULEMINER extra file: skipped (unparsable): {line}"),
        }
    }
    out
}

/// The candidate laws of a miner family (`mul`, `shl`, `lt`, `shr`; the `RULEMINER_*` env vars size them).
pub fn family_laws(family: &str, env: &dyn Fn(&str, usize) -> usize, n: usize, nv: usize, max: u32) -> Vec<(String, Term, Term)> {
    if family == "shl" {
        let conj = shl_conjectures(2);
        let stride = (conj.len() / env("RULEMINER_LAWS", 250)).max(1);
        conj.into_iter().step_by(stride).map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b)).collect()
    } else if family == "shr" {
        // right shifts of the arithmetic pool terms, against every term of the pool and its right shifts
        // RULEMINER_DEEP=1: the depth-2 pool of `terms` (set `MINER_SUB=1` to include `sub`)
        let pool = if env("RULEMINER_DEEP", 0) == 1 { terms(2, true) } else { lt_pool(2) };
        let shr = |a: &Term| Term::Op(SHR1, Box::new(a.clone()), Box::new(Term::Zero));
        let all: Vec<Term> = pool.iter().cloned().chain(pool.iter().map(&shr)).collect();
        pool_conjectures(all, n, nv, 0)
            .into_iter()
            .filter(|(a, b)| a.has_shift() || b.has_shift())
            .step_by(env("RULEMINER_STRIDE", 1))
            .take(env("RULEMINER_LAWS", 250))
            .map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b))
            .collect()
    } else if let Some(pool) = pool3(family, env) {
        pool_conjectures(pool, n, 3, 0)
            .into_iter()
            .filter(|(a, b)| (0..3).all(|v| a.has_var(v) || b.has_var(v)))
            .filter(|(a, b)| env("RULEMINER_SHAPE", 2) == 2 || shape_part(a, b) == env("RULEMINER_SHAPE", 2)) // `RULEMINER_SHAPE=0|1`: one of two structure-based halves
            .skip(env("RULEMINER_PHASE", 0)) // with a stride, the phase picks the residue class: phases 0..stride tile the sequence
            .step_by(env("RULEMINER_STRIDE", 1))
            .skip(env("RULEMINER_SKIP", 0))
            .take(env("RULEMINER_LAWS", 250))
            .map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b))
            .collect()
    } else if family == "lt" {
        let pool = lt_pool(2);
        let all = pool.iter().flat_map(|a| pool.iter().map(move |b| Term::Op(LT, Box::new(a.clone()), Box::new(b.clone()))));
        pool_conjectures(all, n, nv, env("RULEMINER_LAWS", 250)).into_iter().map(|(a, b)| (format!("{} = {}", a.show(), b.show()), a, b)).collect()
    } else {
        mul_laws(max)
    }
}

/// `RULEMINER_SKIP` windows: consecutive windows tile the law sequence, and a window past the end is empty.
#[test]
pub fn family_law_windows_tile_the_sequence() {
    let laws = |skip: usize, take: usize| {
        let env = move |k: &str, d: usize| match k {
            "RULEMINER_SKIP" => skip,
            "RULEMINER_LAWS" => take,
            "RULEMINER_STRIDE" => 1,
            _ => d,
        };
        family_laws("add3", &env, 4, 3, 7).into_iter().map(|(name, _, _)| name).collect::<Vec<_>>()
    };
    let whole = laws(0, 12);
    assert_eq!(whole.len(), 12);
    let mut tiled = laws(0, 5);
    tiled.extend(laws(5, 7));
    assert_eq!(tiled, whole);
    assert!(laws(usize::MAX / 2, 5).is_empty());
}

/// Which of two halves a law belongs to, by the shape of its two sides with variables erased (constants and operators kept):
/// laws that differ only in which variables appear share a half, so near-variants never straddle a split.
/// `RULEMINER_GUARD`: from `clean` machine-free laws, score about `k`: every `step`-th, each standing for `clean / sampled` laws (weight in
/// units of 1000 per straggler), so the sample's net gain estimates the whole window's.
pub fn guard_plan(clean: usize, k: usize) -> (usize, i64) {
    let step = clean.div_ceil(k.max(1)).max(1);
    (step, 1000 * clean as i64 / clean.div_ceil(step).max(1) as i64)
}

#[test]
pub fn guard_plan_samples_and_weights() {
    assert_eq!(guard_plan(538, 120), (5, 4981)); // 108 laws sampled, each standing for about 5
    assert_eq!(guard_plan(100, 1000), (1, 1000)); // k above the count: every law, unit weight
    assert_eq!(guard_plan(100, 100), (1, 1000));
    let (step, w) = guard_plan(7, 3);
    assert_eq!((step, w), (3, 2333)); // laws 0, 3, 6: three laws for seven
    assert_eq!(guard_plan(0, 5).0, 1); // no clean laws: nothing to sample (the caller skips the guard)
}

pub fn shape_part(a: &Term, b: &Term) -> usize {
    shape_part_salted(a, b, &std::env::var("RULEMINER_SHAPE_SALT").unwrap_or_default()) // a different salt gives a different split; unset keeps the original halves
}

fn shape_part_salted(a: &Term, b: &Term, salt: &str) -> usize {
    fn skeleton(t: &Term, out: &mut String) {
        match t {
            Term::V(_) => out.push('v'),
            Term::Zero => out.push('0'),
            Term::Ones => out.push('1'),
            Term::Op(o, x, y) => {
                out.push_str(&format!("({o} "));
                skeleton(x, out);
                out.push(' ');
                skeleton(y, out);
                out.push(')');
            }
        }
    }
    let mut s = salt.to_string();
    skeleton(a, &mut s);
    s.push('=');
    skeleton(b, &mut s);
    // FNV-1a: deterministic across runs and platforms
    let h = s.bytes().fold(0xcbf29ce484222325u64, |h, c| (h ^ c as u64).wrapping_mul(0x100000001b3));
    (h >> 32) as usize & 1
}

/// `RULEMINER_SHAPE`: the two shape halves are disjoint, together are the whole sequence, and renaming variables keeps a law in its half.
#[test]
pub fn family_law_shape_halves_partition() {
    for family in THREE_VAR_FAMILIES {
        shape_halves_partition(family);
    }
}

fn shape_halves_partition(family: &str) {
    let laws = |shape: usize| {
        let env = move |k: &str, d: usize| match k {
            "RULEMINER_SHAPE" => shape,
            "RULEMINER_LAWS" => 100000,
            "RULEMINER_STRIDE" => 1,
            "RULEMINER_DEEP3" => 1,
            _ => d,
        };
        family_laws(family, &env, 4, 3, 7).into_iter().map(|(name, _, _)| name).collect::<std::collections::BTreeSet<_>>()
    };
    let (whole, h0, h1) = (laws(2), laws(0), laws(1));
    println!("shape halves {family}: {} + {} = {}", h0.len(), h1.len(), whole.len());
    assert!(h0.is_disjoint(&h1) && h0.len() + h1.len() == whole.len(), "{} {} {}", h0.len(), h1.len(), whole.len());
    assert!(!h0.is_empty() && !h1.is_empty());
    let (x, y, z) = (parse_term("add(x, y)"), parse_term("add(y, z)"), parse_term("sub(x, z)"));
    assert_eq!(shape_part(&x, &z), shape_part(&y, &z));
}

/// A different salt re-splits the laws (so the split is not one fixed key), and each salt still keeps variable renamings together.
#[test]
pub fn shape_salt_changes_the_split() {
    let laws = ["add(x, y)", "sub(add(x, y), z)", "add(sub(x, y), z)", "sub(x, sub(y, z))", "add(x, sub(y, z))", "sub(xor(x, -1), y)", "add(shl1(x, 0), y)", "sub(add(x, y), xor(z, -1))"];
    let rhs = parse_term("sub(x, y)");
    let half = |salt: &str| laws.iter().map(|l| shape_part_salted(&parse_term(l), &rhs, salt)).collect::<Vec<_>>();
    assert_ne!(half(""), half("a"));
    for salt in ["", "a"] {
        assert_eq!(shape_part_salted(&parse_term("add(x, y)"), &rhs, salt), shape_part_salted(&parse_term("add(y, z)"), &rhs, salt));
    }
}

/// `RULEMINER_PHASE`: with stride 2 the two phases are disjoint and together are the stride-1 sequence.
#[test]
pub fn family_law_phases_are_disjoint() {
    let laws = |stride: usize, phase: usize, take: usize| {
        let env = move |k: &str, d: usize| match k {
            "RULEMINER_STRIDE" => stride,
            "RULEMINER_PHASE" => phase,
            "RULEMINER_LAWS" => take,
            _ => d,
        };
        family_laws("add3", &env, 4, 3, 7).into_iter().map(|(name, _, _)| name).collect::<Vec<_>>()
    };
    let (even, odd, whole) = (laws(2, 0, 6), laws(2, 1, 6), laws(1, 0, 12));
    assert_eq!(even.len() + odd.len(), 12);
    let woven: Vec<String> = even.iter().zip(&odd).flat_map(|(a, b)| [a.clone(), b.clone()]).collect();
    assert_eq!(woven, whole);
}

/// Every `RULEMINER_*` switch of `rule_miner`, read once (defaults in `from_env`).
pub struct MinerConfig {
    /// `MULMINER_MAX`: largest constant in the mul family.
    pub max: u32,
    /// `RULEMINER_TRIALS`: candidate cap.
    pub trials: usize,
    /// `RULEMINER_PERM`: 0 strict rule order, 1 ties broken by `tie_greater`, 2 no order check.
    pub perm: usize,
    /// `RULEMINER_STEPS`: per-law rewrite budget once a base set is loaded.
    pub steps: usize,
    /// `RULEMINER_VARS`: variable cap of cross-side rules.
    pub vars: usize,
    /// `RULEMINER_ROUNDS`: greedy rounds.
    pub rounds: usize,
    /// `RULEMINER_THREADS`: scoring threads, clamped to 1..=12.
    pub threads: usize,
    /// `RULEMINER_ANY`, `_SHOW`, `_FAST`: set to 1 to enable.
    pub any_op: bool,
    pub show: bool,
    pub fast: bool,
}

impl MinerConfig {
    pub fn from_env() -> Self {
        let flag = |k: &str| env_or(k, 0) == 1;
        MinerConfig {
            max: env_or("MULMINER_MAX", 7) as u32,
            trials: env_or("RULEMINER_TRIALS", 400),
            perm: env_or("RULEMINER_PERM", 0),
            steps: env_or("RULEMINER_STEPS", 200),
            vars: env_or("RULEMINER_VARS", 4),
            rounds: env_or("RULEMINER_ROUNDS", 8),
            threads: env_or("RULEMINER_THREADS", 1).clamp(1, 12),
            any_op: flag("RULEMINER_ANY"),
            show: flag("RULEMINER_SHOW"),
            fast: flag("RULEMINER_FAST"),
        }
    }
}

/// Rule miner (search note section 36): candidate rules are the equal pairs of the `shl1` pool (two variables, width 4,
/// the shl miner's pool), oriented to a strictly smaller right side and proved by `add_tree_law`. The targets are the
/// mul laws that still needed a whole-term machine proof under the built-in rules (the "stragglers"). A candidate is
/// tried on the stragglers whose normalized terms contain an instance of its left side; it scores by the machine
/// proofs it removes. Env: `MULMINER_MAX` (default 7), `RULEMINER_TRIALS` (candidate cap, default 400).
#[test]
#[ignore]
pub fn rule_miner() {
    // `<exe>.env` next to the test exe (lines `KEY=VALUE`) sets variables that are not already set, before anything reads the
    // environment: a profiler launcher that cannot pass env (the elevated Samply task) runs the same configuration this way.
    // Main-thread test, no other thread reads env yet.
    if let Ok(text) = std::env::current_exe().map(|mut p| { p.as_mut_os_string().push(".env"); p }).and_then(std::fs::read_to_string) {
        for (k, v) in text.lines().filter_map(|l| l.split_once('=')) {
            if std::env::var_os(k.trim()).is_none() {
                unsafe { std::env::set_var(k.trim(), v.trim()) };
            }
        }
    }
    let _scope = tatic::kernel::InternScope::enter();
    // phase clock: `phase(label)` prints the seconds since the previous mark
    let last = std::cell::Cell::new(Instant::now());
    let phase = |label: &str| {
        println!("RULEMINER time {label}: {:.1}s", last.replace(Instant::now()).elapsed().as_secs_f64());
    };
    println!("RULEMINER machine at start: {}", machine_state());
    let cfg = MinerConfig::from_env();
    let (max, trials) = (cfg.max, cfg.trials);
    // RULEMINER_PERM=1: ties in the rule order are broken by `tie_greater` (reassociation rules; section 70), 2: no order check; the step budget
    // and the same-term check in `rule_step` still back up termination, and soundness is unaffected
    let ok_order = |l: &Term, r: &Term| match cfg.perm {
        0 => rule_order_ok(l, r),
        1 => rule_order_or_tie(l, r),
        _ => true, // 2: no order check at all (the miner's own cross-side rules are not ordered either)
    };
    let family = std::env::var("RULEMINER_FAMILY").unwrap_or_else(|_| "mul".into());
    // RULEMINER_BASE=<file>: rules (`lhs -> rhs` lines) in force throughout, the stragglers are those left with them (section 74)
    let base: Vec<(Term, Term)> = std::env::var("RULEMINER_BASE").ok().map(|f| parse_rules(&std::fs::read_to_string(f).unwrap())).unwrap_or_default();
    EXTRA_RULES.with(|e| *e.borrow_mut() = base.clone());
    // `add3` laws have three variables (the candidate generator below still builds patterns over at most two)
    let (n, nv, kv) = (4usize, 2usize, if family_vars(&family) == 3 { 3usize } else { 2 });
    let ops = ops_for(n);
    let goods: Vec<(Expr, Expr)> = (0..kv).map(|i| (var((2 * kv - 1 - i) as u32), var((kv - 1 - i) as u32))).collect();
    let fallbacks = || MACHINE_FALLBACKS.with(|c| c.get());
    // stragglers under the built-in rules
    let mut stragglers: Vec<(String, Term, Term, [Term; 2], u64, std::time::Duration)> = vec![];
    let laws = family_laws(&family, &env_or::<usize>, n, nv, max);
    let mut unproved = 0usize;
    let mut clean: Vec<(String, Term, Term)> = vec![]; // laws that are already machine-free under the base rules (for `RULEMINER_GUARD`)
    for (name, t1, t2) in laws.iter().cloned() {
        if !(1..=6).all(|w| t1.plausibly_equals(&t2, w, kv)) || [&t1, &t2].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap())) {
            continue;
        }
        let before = fallbacks();
        let t = Instant::now();
        // base rules may loop; the step budget bounds them (the built-in rules never reach it)
        RULE_BUDGET.with(|b| b.set(if base.is_empty() { i64::MAX / 2 } else { cfg.steps as i64 }));
        let r = rewrite_law(n, kv, &t1, &t2);
        let took = t.elapsed();
        let fell = fallbacks() - before;
        // a law the rewriter cannot close at all counts as a straggler too (fixed once it is proved machine-free)
        unproved += r.is_none() as usize;
        let fell = if r.is_none() { fell.max(1) } else { fell };
        if r.is_none() || fell > 0 {
            RULE_BUDGET.with(|b| b.set(if base.is_empty() { i64::MAX / 2 } else { cfg.steps as i64 }));
            let normal = [rewrite(&t1, n, &ops, &goods).0, rewrite(&t2, n, &ops, &goods).0];
            println!("RULEMINER straggler {name}: {} = {} ({fell} machine proofs, {took:?}{})", normal[0].show(), normal[1].show(), if r.is_none() { ", UNPROVED" } else { "" });
            stragglers.push((name, t1, t2, normal, fell, took));
        } else {
            clean.push((name, t1, t2));
        }
    }
    let base_time: f64 = stragglers.iter().map(|s| s.5.as_secs_f64()).sum();
    println!("RULEMINER {family}: {} stragglers of {} laws, {:.1}s base ({unproved} unproved)", stragglers.len(), laws.len(), base_time);
    phase("laws and stragglers");
    // `RULEMINER_GUARD=<k>` (default 120, 0 = off): about k of the already machine-free laws are scored with the stragglers, so a candidate that breaks them loses
    // the same 1000 per law as it gains per straggler fixed (the miner otherwise sees only the stragglers and cannot see a regression)
    let guard_k = env_or("RULEMINER_GUARD", 120); // default 120; 0 turns the check off
    let mut scored = stragglers.clone();
    let mut guard_w = 1000i64; // each sampled guard law stands for clean/sampled laws, so a regression costs that many times 1000
    if guard_k > 0 && !clean.is_empty() {
        let (step, w) = guard_plan(clean.len(), guard_k);
        guard_w = w;
        for (name, t1, t2) in clean.iter().step_by(step) {
            scored.push((name.clone(), t1.clone(), t2.clone(), [t1.clone(), t2.clone()], 1, std::time::Duration::ZERO));
        }
        println!("RULEMINER guard: {} machine-free laws scored of {} (weight {guard_w} each)", scored.len() - stragglers.len(), clean.len());
    }
    // goal-directed candidates: abstract each arithmetic subterm of a straggler's normalized terms into a pattern over
    // at most two variables (cutting subterms into variables), and look for a smaller term over the same variables
    // with the same values at width 4 (a pool of all terms up to 5 nodes, indexed by value)
    let psize = 5;
    let mut by_size: Vec<Vec<Term>> = vec![vec![]; psize + 1];
    by_size[1] = vec![Term::V(0), Term::V(1), Term::Zero, Term::Ones];
    for sz in 2..=psize {
        let mut level = vec![];
        for x in &by_size[sz - 1] {
            level.push(Term::Op(SHL1, Box::new(x.clone()), Box::new(Term::Zero)));
            level.push(Term::Op(SHR1, Box::new(x.clone()), Box::new(Term::Zero)));
        }
        for i in 1..sz - 1 {
            for l in &by_size[i] {
                for r in &by_size[sz - 1 - i] {
                    for o in [0usize, 1, 2, 3, 4] {
                        level.push(Term::Op(o, Box::new(l.clone()), Box::new(r.clone())));
                    }
                }
            }
        }
        by_size[sz] = level;
    }
    let sig = |t: &Term| -> Vec<u128> { (0..1u128 << (4 * kv)).map(|i| t.interp(n, &(0..kv).map(|v| i >> (4 * v) & 15).collect::<Vec<_>>())).collect() };
    let mut index: std::collections::HashMap<Vec<u128>, Vec<Term>> = Default::default();
    for t in by_size.iter().flatten() {
        index.entry(sig(t)).or_default().push(t.clone());
    }
    // `lt` terms (one-bit values) only as roots, indexed apart: their 0/1 values must not meet the n-bit constants
    let mut index_lt: std::collections::HashMap<Vec<u128>, Vec<Term>> = Default::default();
    for a in by_size.iter().take(4).flatten() {
        for b in by_size.iter().take(4).flatten() {
            let t = Term::Op(LT, Box::new(a.clone()), Box::new(b.clone()));
            index_lt.entry(sig(&t)).or_default().push(t);
        }
    }
    println!("RULEMINER pool of {} terms, {} distinct functions", by_size.iter().map(|v| v.len()).sum::<usize>(), index.len());
    /// The patterns obtained from `t` by cutting subterms into variables: (pattern, cut subterms in variable order).
    fn abstractions(t: &Term, cap: usize) -> Vec<(Term, Vec<Term>)> {
        let mut out = vec![];
        if !matches!(t, Term::Zero | Term::Ones) {
            out.push((Term::V(0), vec![t.clone()]));
        } else {
            out.push((t.clone(), vec![]));
        }
        if let Term::Op(o, a, b) = t {
            for (pa, ca) in abstractions(a, cap) {
                for (pb, cb) in abstractions(b, cap) {
                    // renumber the right pattern's variables after the left's, merging equal cut subterms
                    let mut cuts = ca.clone();
                    let mut map = vec![];
                    for c in &cb {
                        let at = cuts.iter().position(|x| x.show() == c.show()).unwrap_or_else(|| {
                            cuts.push(c.clone());
                            cuts.len() - 1
                        });
                        map.push(at);
                    }
                    if cuts.len() > cap {
                        continue;
                    }
                    fn renum(p: &Term, map: &[usize]) -> Term {
                        match p {
                            Term::V(i) => Term::V(map[*i]),
                            Term::Op(o, a, b) => Term::Op(*o, Box::new(renum(a, map)), Box::new(renum(b, map))),
                            _ => p.clone(),
                        }
                    }
                    out.push((Term::Op(*o, Box::new(pa.clone()), Box::new(renum(&pb, &map))), cuts));
                }
            }
        }
        out.retain(|(_, c)| c.len() <= cap);
        out
    }
    // RULEMINER_ANY=1: also abstract subterms without add/sub (constant folding inside shifts and bitwise nodes)
    let any_op = cfg.any_op;
    let mut seen_pat: std::collections::HashSet<String> = Default::default();
    let mut cands: Vec<(Term, Term)> = vec![];
    for st in &stragglers {
        let mut subs = vec![];
        st.3[0].subterms(&mut subs);
        st.3[1].subterms(&mut subs);
        for sub in subs.iter().filter(|t| matches!(t, Term::Op(LT, ..)) || (any_op || t.uses_add()) && t.size() >= if any_op { 2 } else { 3 }) {
            for (pat, _) in abstractions(sub, 2) {
                let Term::Op(..) = pat else { continue };
                if !seen_pat.insert(pat.show()) || pat.size() > 9 {
                    continue;
                }
                let is_lt = matches!(pat, Term::Op(LT, ..));
                let Some(group) = (if is_lt { &index_lt } else { &index }).get(&sig(&pat)) else { continue };
                let uses = |t: &Term, v: usize| t.has_var(v);
                let _ = is_lt;
                for r in group.iter().filter(|r| ok_order(&pat, r) && (0..2).all(|v| !uses(r, v) || uses(&pat, v))) {
                    cands.push((pat.clone(), r.clone()));
                }
            }
        }
    }
    // cross-side candidates: a subterm of one normalized side and a subterm of the other with the same value, both
    // abstracted by the same cuts (up to four variables): the rule `abstract(s) -> abstract(s')`
    let cross_cap = cfg.vars;
    for st in &stragglers {
        let (mut sl, mut sr) = (vec![], vec![]);
        st.3[0].subterms(&mut sl);
        st.3[1].subterms(&mut sr);
        for (xs, ys) in [(&sl, &sr), (&sr, &sl)] {
            for x in xs.iter().filter(|t| t.uses_add() && t.size() >= 3 && t.size() <= 13) {
                for y in ys.iter().filter(|t| t.size() <= 13 && t.show() != x.show()) {
                    if !(1..=4).all(|w| x.plausibly_equals(y, w, kv)) {
                        continue;
                    }
                    for (pat, cuts) in abstractions(x, cross_cap) {
                        let Term::Op(..) = pat else { continue };
                        if cuts.len() <= 2 || pat.size() > 13 {
                            continue; // up to two variables is the pool route's job
                        }
                        // express y with the same cuts, through placeholders V(4+j)
                        let mut yy = y.clone();
                        for (j, c) in cuts.iter().enumerate() {
                            yy = replace_term(&yy, c, &Term::V(4 + j));
                        }
                        fn bare(t: &Term) -> bool {
                            match t {
                                Term::V(i) => *i >= 4,
                                Term::Op(_, a, b) => bare(a) && bare(b),
                                _ => true,
                            }
                        }
                        fn renum(t: &Term) -> Term {
                            match t {
                                Term::V(i) => Term::V(i - 4),
                                Term::Op(o, a, b) => Term::Op(*o, Box::new(renum(a)), Box::new(renum(b))),
                                _ => t.clone(),
                            }
                        }
                        if bare(&yy) && yy.size() < pat.size() + 4 && seen_pat.insert(format!("{} => {}", pat.show(), renum(&yy).show())) {
                            cands.push((pat.clone(), renum(&yy)));
                        }
                    }
                }
            }
        }
    }
    // `RULEMINER_EXTRA=<file>`: extra candidates (`lhs -> rhs` lines) joining the miner's own, before the one-per-left-side pass
    if let Ok(path) = std::env::var("RULEMINER_EXTRA") {
        let extra = read_rule_file(&path);
        println!("RULEMINER {} extra candidates from {path}", extra.len());
        cands.extend(extra);
    }
    // `RULEMINER_NODUPLHS` (default on, 0 = off): drop candidates whose left side already has a rule in force (`RULEMINER_BASE`); the one-per-left-side pass
    // below only sees this mine's candidates, so a later mine could otherwise add a second, competing rewrite for the same pattern
    if std::env::var("RULEMINER_NODUPLHS").map_or(true, |v| v != "0") {
        let before = cands.len();
        let in_force: std::collections::HashSet<String> = base.iter().map(|(l, _)| l.show()).collect();
        cands.retain(|(l, _)| !in_force.contains(&l.show()));
        println!("RULEMINER dropped {} candidates whose left side is already in force", before - cands.len());
    }
    // per left side, the smallest right side only
    cands.sort_by_key(|(l, r)| (l.size(), l.show(), r.size(), r.show()));
    cands.dedup_by_key(|(l, _)| l.show());
    println!("RULEMINER {} oriented candidates (one per left side)", cands.len());
    phase("candidate generation");
    // keep candidates whose left side matches a subterm of some straggler's normalized terms
    let applicable = |l: &Term| {
        stragglers.iter().any(|s| {
            let mut subs = vec![];
            s.3[0].subterms(&mut subs);
            s.3[1].subterms(&mut subs);
            subs.iter().any(|t| match_pat(l, t, &mut vec![None; 8]))
        })
    };
    let cands: Vec<(Term, Term)> = cands.into_iter().filter(|(l, _)| applicable(l)).take(trials).collect();
    println!("RULEMINER {} applicable candidates (cap {trials})", cands.len());
    if cfg.show {
        for (l, r) in &cands {
            println!("RULEMINER candidate: {} -> {}", l.show(), r.show());
        }
    }
    // cumulative greedy: each round adds the candidate that, on top of the rules chosen so far, fixes the most
    // stragglers (no whole-term machine proof) and then shrinks the normalized terms most; a straggler often needs two
    // rules together, which a one-rule-at-a-time score cannot see
    let provable: Vec<&(Term, Term)> = cands.iter().filter(|(l, r)| prove_rule(n, l.max_var().max(r.max_var()) + 1, l, r).is_some()).collect();
    println!("RULEMINER {} provable candidates of {} proposed", provable.len(), cands.len());
    phase("provable filter");
    let score = |extra: &[(Term, Term)]| -> (Vec<bool>, i64) {
        // built here so that worker threads (each with its own intern scope) do not share expressions
        let ops = ops_for(n);
        let goods: Vec<(Expr, Expr)> = (0..kv).map(|i| (var((2 * kv - 1 - i) as u32), var((kv - 1 - i) as u32))).collect();
        let fallbacks = || MACHINE_FALLBACKS.with(|c| c.get());
        EXTRA_RULES.with(|e| *e.borrow_mut() = base.iter().chain(extra).cloned().collect());
        let steps = cfg.steps as i64;
        let budget = || RULE_BUDGET.with(|b| b.set(steps));
        SCORE_ONLY.with(|s| s.set(cfg.fast));
        let (mut fixed, mut size) = (vec![false; scored.len()], 0i64);
        for (si, s) in scored.iter().enumerate() {
            budget();
            let before = fallbacks();
            let ok = rewrite_law(n, kv, &s.1, &s.2).is_some();
            fixed[si] = ok && fallbacks() - before < s.4;
            budget();
            // the rule order's own measure: operator nodes first, then variable occurrences
            let measure = |t: &Term| {
                let mut occ = [0usize; 8];
                t.occurrences(&mut occ);
                let (c, a) = rule_weight(t);
                (c + a.iter().sum::<i64>()) * 16 + occ.iter().sum::<usize>() as i64
            };
            if si < stragglers.len() {
                size += measure(&rewrite(&s.1, n, &ops, &goods).0) + measure(&rewrite(&s.2, n, &ops, &goods).0);
            }
        }
        SCORE_ONLY.with(|s| s.set(false));
        EXTRA_RULES.with(|e| e.borrow_mut().clear());
        RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
        (fixed, size)
    };
    let mut chosen: Vec<(Term, Term)> = vec![];
    let (mut covered, mut size) = score(&chosen);
    for _ in 0..cfg.rounds {
        let count = |f: &Vec<bool>| f.iter().take(stragglers.len()).filter(|c| **c).count() as i64;
        let guarded = |f: &Vec<bool>| f.iter().skip(stragglers.len()).filter(|c| **c).count() as i64;
        let mut best: Option<ScoredRule> = None;
        // the candidates are scored on `RULEMINER_THREADS` workers (default 1; keep at most 12), each with its own intern
        // scope; the results are folded in candidate order, so the choice does not depend on the thread count
        let threads = cfg.threads.clamp(1, 12);
        let scored: Vec<(Vec<bool>, i64)> = {
            let run = |idx: &[usize]| -> Vec<(usize, (Vec<bool>, i64))> {
                let _scope = tatic::kernel::InternScope::enter();
                idx.iter()
                    .map(|&i| {
                        let mut with = chosen.clone();
                        with.push(provable[i].clone());
                        (i, score(&with))
                    })
                    .collect()
            };
            let mut all: Vec<(usize, (Vec<bool>, i64))> = if threads == 1 {
                run(&(0..provable.len()).collect::<Vec<_>>())
            } else {
                std::thread::scope(|sc| {
                    let handles: Vec<_> = (0..threads)
                        .map(|t| {
                            let idx: Vec<usize> = (t..provable.len()).step_by(threads).collect();
                            let run = &run;
                            std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, move || run(&idx)).unwrap()
                        })
                        .collect();
                    handles.into_iter().flat_map(|h| h.join().unwrap()).collect()
                })
            };
            all.sort_by_key(|x| x.0);
            all.into_iter().map(|x| x.1).collect()
        };
        for (cand, (f, sz)) in provable.iter().zip(scored) {
            let raw = (count(&f) - count(&covered)) * 1000 + (guarded(&f) - guarded(&covered)) * guard_w + (size - sz);
            if raw > 0 && best.as_ref().is_none_or(|b| raw > b.0) {
                best = Some((raw, (*cand).clone(), f, sz));
            }
        }
        let Some((_, rule, f, sz)) = best else { break };
        println!("RULEMINER chosen (+{} fixed, -{} size): {} -> {}", count(&f) - count(&covered), size - sz, rule.0.show(), rule.1.show());
        phase(&format!("round over {} candidates", provable.len()));
        chosen.push(rule);
        (covered, size) = (f, sz);
    }
    println!("RULEMINER {} of {} stragglers covered by the chosen rules", covered.iter().take(stragglers.len()).filter(|c| **c).count(), stragglers.len());
    for (st, c) in stragglers.iter().zip(&covered) {
        if !c {
            println!("RULEMINER uncovered: {}", st.0);
        }
    }
    println!("RULEMINER machine at end: {}", machine_state());
}

/// `bitwise_law_k` dispatches to the per-position prover when a shift occurs: shl1 distributes over the bitwise
/// operators, and a false shift law fails to check.
#[test]
pub fn bitwise_law_proves_shift_laws_and_rejects_false_ones() {
    let _scope = tatic::kernel::InternScope::enter();
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let shl = |a: Term| op(6, a, Term::Zero);
    let (x, y) = (Term::V(0), Term::V(1));
    for n in [3, 4] {
        for o in 1..=3 {
            let (p, s) = bitwise_law_k(n, 2, &shl(op(o, x.clone(), y.clone())), &op(o, shl(x.clone()), shl(y.clone())));
            ck("shl over bitwise", &p, &s);
        }
        let (p, s) = bitwise_law_k(n, 2, &shl(x.clone()), &x);
        assert!(check(&Ctx::new(), &p, &s).is_err(), "shl x = x must fail");
    }
}

/// `read_rule_file` (behind `RULEMINER_EXTRA`) parses `lhs -> rhs` lines and skips comments and blanks.
#[test]
pub fn extra_candidates_are_merged() {
    let path = std::env::temp_dir().join(format!("extra_candidates_{}.txt", std::process::id()));
    std::fs::write(&path, "# comment\n\nadd(sub(x, y), z) -> add(sub(z, y), x)\nand(x, x) -> x\n").unwrap();
    let rules = read_rule_file(path.to_str().unwrap());
    std::fs::remove_file(&path).ok();
    let shown: Vec<(String, String)> = rules.iter().map(|(l, r)| (l.show(), r.show())).collect();
    assert_eq!(shown.len(), 2, "{shown:?}");
    assert_eq!(shown[0], (parse_term("add(sub(x, y), z)").show(), parse_term("add(sub(z, y), x)").show()));
    assert_eq!(shown[1], (parse_term("and(x, x)").show(), parse_term("x").show()));
}

#[test]
pub fn notsub_rule_is_provable() {
    let _scope = tatic::kernel::InternScope::enter();
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    for n in [3, 4] {
        let r = prove_rule(n, 1, &op(3, Term::V(0), Term::Ones), &op(4, Term::Ones, Term::V(0)));
        let (p, s) = r.expect("xor(x, -1) = sub(-1, x)");
        ck("notsub", &p, &s);
    }
}

/// `rewrite_law` closes `lt` laws: operands rewritten under the root, then congruence; a false law is refused.
#[test]
pub fn rewrite_law_proves_lt_laws() {
    let _scope = tatic::kernel::InternScope::enter();
    let (x, y) = (Term::V(0), Term::V(1));
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let n = 4;
    for (name, t1, t2) in [
        ("lt (x + 0) y = lt x y", op(5, op(0, x.clone(), Term::Zero), y.clone()), op(5, x.clone(), y.clone())),
        ("lt (x + y) y = lt (y + x) y", op(5, op(0, x.clone(), y.clone()), y.clone()), op(5, op(0, y.clone(), x.clone()), y.clone())),
        ("lt (x + y) (x + x) = lt (y + x) (x + x)", op(5, op(0, x.clone(), y.clone()), op(0, x.clone(), x.clone())), op(5, op(0, y.clone(), x.clone()), op(0, x.clone(), x.clone()))),
    ] {
        let (p, s) = rewrite_law(n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no proof"));
        ck(name, &p, &s);
    }
    assert!(rewrite_law(n, 2, &op(5, x.clone(), y.clone()), &op(5, y.clone(), x.clone())).is_none());
}

#[test]
pub fn lt_rules_with_constant_right_sides_are_provable() {
    let _scope = tatic::kernel::InternScope::enter();
    let lt = |a: Term, b: Term| Term::Op(LT, Box::new(a), Box::new(b));
    let n = 4;
    for k in [1usize, 2] {
        for (l, r) in [(lt(Term::Ones, Term::V(0)), lt(Term::Ones, Term::Ones)), (lt(Term::V(0), Term::V(0)), lt(Term::Ones, Term::Ones))] {
            let (p, s) = prove_rule(n, k, &l, &r).unwrap_or_else(|| panic!("k={k}: {} -> {}", l.show(), r.show()));
            ck("lt rule", &p, &s);
        }
    }
}

/// Two root rules close `lt(x, x) = lt(-1, x + y)` without a machine proof of the whole law.
#[test]
pub fn lt_root_rules_close_constant_false_laws() {
    let _scope = tatic::kernel::InternScope::enter();
    let (x, y) = (Term::V(0), Term::V(1));
    let lt = |a: Term, b: Term| Term::Op(LT, Box::new(a), Box::new(b));
    let add = |a: Term, b: Term| Term::Op(ADD, Box::new(a), Box::new(b));
    let falsum = lt(Term::Ones, Term::Ones);
    EXTRA_RULES.with(|e| *e.borrow_mut() = vec![(lt(x.clone(), x.clone()), falsum.clone()), (lt(Term::Ones, x.clone()), falsum.clone())]);
    let before = MACHINE_FALLBACKS.with(|c| c.get());
    let r = rewrite_law(4, 2, &lt(x.clone(), x.clone()), &lt(Term::Ones, add(x.clone(), y.clone())));
    let fell = MACHINE_FALLBACKS.with(|c| c.get()) - before;
    EXTRA_RULES.with(|e| e.borrow_mut().clear());
    let (p, s) = r.expect("proved");
    ck("lt(x,x) = lt(-1, x+y)", &p, &s);
    assert_eq!(fell, 0, "no whole-term machine proof");
}

#[test]
pub fn shr_mask_proves_root_shift_laws_over_arithmetic_and_rejects_false_ones() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = Term::V;
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let shr = |a: Term| op(7, a, Term::Zero);
    let laws = [
        // closed argument: shr1 1 = 0
        (Term::Zero, shr(op(4, Term::Zero, Term::Ones))),
        // the arguments differ only in bit 0
        (shr(op(0, v(0), v(0))), shr(op(4, op(0, v(0), v(0)), Term::Ones))),
        (shr(op(0, op(4, v(0), Term::Ones), v(1))), shr(op(4, op(0, v(0), v(1)), Term::Ones))),
        // shifts the rewriter pushes down to atoms (`shr1 (1)`, `shr1 -1`): closed by the mask on the original sides
        (Term::Zero, shr(op(1, op(4, Term::Zero, Term::Ones), v(1)))),
        (shr(op(1, op(3, v(0), v(1)), v(0))), shr(op(1, v(0), op(3, v(1), Term::Ones)))),
    ];
    for n in [1usize, 3, 4] {
        for (l, r) in &laws {
            let (p, s) = rewrite_law(n, 2, l, r).unwrap_or_else(|| panic!("no proof: {} = {} at n={n}", l.show(), r.show()));
            ck(&format!("{} = {} at n={n}", l.show(), r.show()), &p, &s);
        }
    }
    // not laws: the arguments differ above bit 0
    for (l, r) in [(shr(op(0, v(0), v(1))), shr(op(0, v(0), v(0)))), (Term::Zero, shr(op(0, v(0), Term::Ones)))] {
        assert!(rewrite_law(4, 2, &l, &r).is_none(), "{} = {}", l.show(), r.show());
    }
}

/// Lemma ablation, end to end (search note section 51): the library lemmas `add x 0 = x`, `add 0 x = x`, `add x y = add y x`,
/// `add x ~x = -1` and associativity are proved from the statement alone, by the Moore-refinement encoding search inside
/// `add_tree_law` (no rewrite rule, no hand-written invariant), and checked by the kernel at several widths.
#[test]
pub fn encoding_search_rediscovers_library_lemmas_from_statements() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = Term::V;
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let laws = [
        ("add x 0 = x", 1, op(0, v(0), Term::Zero), v(0)),
        ("add 0 x = x", 1, op(0, Term::Zero, v(0)), v(0)),
        ("add x y = add y x", 2, op(0, v(0), v(1)), op(0, v(1), v(0))),
        ("add x ~x = -1", 1, op(0, v(0), op(3, v(0), Term::Ones)), Term::Ones),
        ("add (add x y) z = add x (add y z)", 3, op(0, op(0, v(0), v(1)), v(2)), op(0, v(0), op(0, v(1), v(2)))),
    ];
    for n in [1usize, 3, 4] {
        for (name, k, l, r) in &laws {
            let (p, s) = add_tree_law(n, *k, l, r).unwrap_or_else(|| panic!("no proof: {name} at n={n}"));
            ck(&format!("{name} at n={n}"), &p, &s);
        }
    }
    // a non-law is refused
    assert!(add_tree_law(4, 2, &op(0, v(0), v(1)), &op(0, v(0), v(0))).is_none());
}

// ---- Variable multiplication as a circuit (search note section 58, goal D option b): `mul x y` as shift-and-add
// partial products over bits, `row_i[j] = y_i & x_(j-i)`, summed by ripple adders. Laws are proved per width by case
// analysis on all 2n input bits with `refl` leaves, so they are finite and compare circuits only (no numeric meaning).

/// `\a b. \C k. a C (\a_i.. b C (\b_i.. k out_0 .. out_(n-1)))` where `outs(a_bits, b_bits)` gives the output bits.
pub fn bits_circuit(n: usize, outs: BitsFn) -> Expr {
    let d = 4 + 2 * n;
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let a: Vec<Expr> = (0..n).map(|i| v(4 + i)).collect();
    let b: Vec<Expr> = (0..n).map(|i| v(4 + n + i)).collect();
    let mut body = apps(v(3), outs(&a, &b));
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(n), app2(var(3), var(1), inner)))))
}

pub fn add_rows(a: &[Expr], b: &[Expr]) -> Vec<Expr> {
    let mut carry = f();
    let mut sums = vec![];
    for i in 0..a.len() {
        let x = xor(a[i].clone(), b[i].clone());
        sums.push(xor(x.clone(), carry.clone()));
        carry = ripple_carry(false, a[i].clone(), b[i].clone(), carry, x);
    }
    sums
}

pub type BitsFn<'a> = &'a dyn Fn(&[Expr], &[Expr]) -> Vec<Expr>;
pub type KBitsFn<'a> = &'a dyn Fn(&[Vec<Expr>]) -> Vec<Expr>;

/// `Pi x y. GoodBv x -> GoodBv y -> Id(Bv_n, L x y, R x y)` where `L`, `R` are the circuits of the output-bit
/// functions `l`, `r` of the `n` bits of `x` and of `y`. Per output bit, case analysis on all `2n` input bits with
/// `refl` leaves, then `cong_n` and the witness eliminations (the skeleton of `bitwise_law_k`).
pub fn circuit_law(n: usize, l: BitsFn, r: BitsFn) -> (Expr, Expr) {
    let (lc, rc) = (bits_circuit(n, l), bits_circuit(n, r));
    circuit_law_k(n, 2, &|a| (app2(lc.clone(), a[0].clone(), a[1].clone()), app2(rc.clone(), a[0].clone(), a[1].clone())), &|v| l(&v[0], &v[1]), &|v| r(&v[0], &v[1]))
}

/// As `circuit_law` over `k` vectors: `sides(vectors)` builds the two sides from circuits, `l`/`r` give their output
/// bits from the `k` vectors' bits (the sides must reduce to those bits by conversion).
pub fn circuit_law_k(n: usize, k: usize, sides: &dyn Fn(&[Expr]) -> (Expr, Expr), l: KBitsFn, r: KBitsFn) -> (Expr, Expr) {
    let split = |v: &[Expr]| -> Vec<Vec<Expr>> { (0..k).map(|i| v[i * n..(i + 1) * n].to_vec()).collect() };
    let lemmas: Vec<Expr> = (0..n)
        .map(|j| {
            lemma_n(
                k * n,
                &|v| id(bool0(), l(&split(v))[j].clone(), r(&split(v))[j].clone()),
                &|b| refl(l(&split(&b.iter().map(|x| bit(*x)).collect::<Vec<_>>()))[j].clone()),
            )
            .0
        })
        .collect();
    k_var_law_to(n, k, &bv_ty(n), sides, &|bits, goods| {
        let vb: Vec<Vec<Expr>> = (0..k).map(|v| (0..n).map(|i| bits(v, i)).collect()).collect();
        let (s1, s2) = (l(&vb), r(&vb));
        let witnesses: Vec<Expr> = (0..k).flat_map(|v| (0..n).map(move |i| (v, i))).map(|(v, i)| goods(v, i)).collect();
        let e = (0..n).map(|j| apps(lemmas[j].clone(), vb.iter().flatten().cloned().chain(witnesses.iter().cloned()).collect())).collect();
        let mut fbody = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
        fbody = lam(sort(1), lam(karrow(n), fbody));
        for _ in 0..n {
            fbody = lam(bool0(), fbody);
        }
        cong_n(&bool0(), &bv_ty(n), &fbody, &s1, &s2, e)
    })
}

pub fn mul_bits(n: usize, x: &[Expr], y: &[Expr]) -> Vec<Expr> {
    let row = |i: usize| -> Vec<Expr> { (0..n).map(|j| if j < i { f() } else { and(y[i].clone(), x[j - i].clone()) }).collect() };
    (1..n).fold(row(0), |acc, i| add_rows(&acc, &row(i)))
}
pub fn const_bits(n: usize, c: u128) -> Vec<Expr> {
    (0..n).map(|i| bit((c >> i) & 1 == 1)).collect()
}

#[test]
pub fn mul_circuit_laws_by_case_analysis_and_false_ones_rejected() {
    for n in [2usize, 3, 4] {
        let _scope = tatic::kernel::InternScope::enter();
        let m = |x: &[Expr], y: &[Expr]| mul_bits(n, x, y);
        let t0 = Instant::now();
        let laws: Vec<(&str, Box<BitsDyn>, Box<BitsDyn>)> = vec![
            ("mul x y = mul y x", Box::new(move |x, y| mul_bits(n, x, y)), Box::new(move |x, y| mul_bits(n, y, x))),
            ("mul x 1 = x", Box::new(move |x, _| mul_bits(n, x, &const_bits(n, 1))), Box::new(|x, _| x.to_vec())),
            ("mul x 0 = 0", Box::new(move |x, _| mul_bits(n, x, &const_bits(n, 0))), Box::new(move |_, _| const_bits(n, 0))),
            ("mul x 2 = add x x", Box::new(move |x, _| mul_bits(n, x, &const_bits(n, 2))), Box::new(|x, _| add_rows(x, x))),
        ];
        for (name, l, r) in &laws {
            let (p, s) = circuit_law(n, &**l, &**r);
            ck(&format!("{name} n={n}"), &p, &s);
            println!("MUL {name} n={n}: {:?}", t0.elapsed());
        }
        let (p, s) = circuit_law(n, &m, &|x, y| add_rows(x, y));
        assert!(check(&Ctx::new(), &p, &s).is_err(), "mul = add must be rejected, n={n}");
    }
}

/// Three-vector laws: `mul` distributes over `add`, and is associative (circuits composed from the two-vector ones).
#[test]
pub fn mul_circuit_three_vector_laws() {
    for n in [2usize, 3] {
        let _scope = tatic::kernel::InternScope::enter();
        let (mc, ac) = (bits_circuit(n, &move |x, y| mul_bits(n, x, y)), bits_circuit(n, &|x, y| add_rows(x, y)));
        let t0 = Instant::now();
        let dist = circuit_law_k(
            n,
            3,
            &|a| (app2(mc.clone(), a[0].clone(), app2(ac.clone(), a[1].clone(), a[2].clone())), app2(ac.clone(), app2(mc.clone(), a[0].clone(), a[1].clone()), app2(mc.clone(), a[0].clone(), a[2].clone()))),
            &|v| mul_bits(n, &v[0], &add_rows(&v[1], &v[2])),
            &|v| add_rows(&mul_bits(n, &v[0], &v[1]), &mul_bits(n, &v[0], &v[2])),
        );
        ck(&format!("mul distributes n={n}"), &dist.0, &dist.1);
        let assoc = circuit_law_k(
            n,
            3,
            &|a| (app2(mc.clone(), app2(mc.clone(), a[0].clone(), a[1].clone()), a[2].clone()), app2(mc.clone(), a[0].clone(), app2(mc.clone(), a[1].clone(), a[2].clone()))),
            &|v| mul_bits(n, &mul_bits(n, &v[0], &v[1]), &v[2]),
            &|v| mul_bits(n, &v[0], &mul_bits(n, &v[1], &v[2])),
        );
        ck(&format!("mul assoc n={n}"), &assoc.0, &assoc.1);
        println!("MUL3 n={n}: {:?}", t0.elapsed());
        // false: x * (y + z) = x * y + z
        let bad = circuit_law_k(
            n,
            3,
            &|a| (app2(mc.clone(), a[0].clone(), app2(ac.clone(), a[1].clone(), a[2].clone())), app2(ac.clone(), app2(mc.clone(), a[0].clone(), a[1].clone()), a[2].clone())),
            &|v| mul_bits(n, &v[0], &add_rows(&v[1], &v[2])),
            &|v| add_rows(&mul_bits(n, &v[0], &v[1]), &v[2]),
        );
        assert!(check(&Ctx::new(), &bad.0, &bad.1).is_err(), "false distributivity must be rejected, n={n}");
    }
}

/// Whether `l -> r` decreases in the rule order and is provable at widths 3 and 4 (the admission test for a rule).
pub fn rule_admissible(l: &Term, r: &Term) -> bool {
    rule_order_ok(l, r) && [3usize, 4].iter().all(|&n| prove_rule(n, l.max_var().max(r.max_var()) + 1, l, r).is_some())
}

#[test]
pub fn promoted_rules_are_ordered_and_provable() {
    let _scope = tatic::kernel::InternScope::enter();
    for (l, r) in promoted_rules() {
        assert_eq!(parse_term(&l.show()).show(), l.show());
        assert!(rule_admissible(l, r), "{} -> {} is not decreasing in the rule order or not provable at widths 3 and 4", l.show(), r.show());
    }
}

/// The admission test refuses wrong rules: every promoted rule with its right side replaced by another promoted rule's
/// right side over the same variables (so it stays well-formed and, where the order allows, decreasing) is refused unless
/// it happens to be a true law.
#[test]
pub fn rule_admission_refuses_wrong_rules() {
    let _scope = tatic::kernel::InternScope::enter();
    let rs = promoted_rules();
    let (mut refused, mut tried) = (0, 0);
    for (l, _) in rs {
        for (_, r) in rs {
            let vars = |t: &Term| (0..8).filter(|v| t.has_var(*v)).collect::<Vec<_>>();
            if vars(r).iter().any(|v| !vars(l).contains(v)) || l.size() <= r.size() {
                continue;
            }
            tried += 1;
            let true_law = (1..=6).all(|w| l.plausibly_equals(r, w, 2));
            if !true_law {
                assert!(!rule_admissible(l, r), "wrong rule admitted: {} -> {}", l.show(), r.show());
                refused += 1;
            }
        }
    }
    println!("ADMISSION {refused} wrong rules refused of {tried} tried");
    assert!(refused > 50, "too few wrong rules exercised: {refused}");
}

/// Probe (search note section 61): the 7 non-constant `lt` stragglers restated through the borrow bit, at width 4.
/// `lt(a, b)` is the top bit of `B(a, b) = (~a & b) | (~(a ^ b) & (a - b))`, so `lt(a, b) = lt(c, d)` becomes the
/// shift-free law `B(a, b) & TOP = B(c, d) & TOP` (`TOP` = 8). Prints, per law, whether the rewriter proves it and how many
/// whole-term machine proofs it still needed, next to the same count for the `lt` form.
#[test]
#[ignore]
pub fn lt_borrow_bit_probe() {
    let _scope = tatic::kernel::InternScope::enter();
    let b = |o: usize, a: Term, c: Term| Term::Op(o, Box::new(a), Box::new(c));
    let not = |a: Term| b(3, a, Term::Ones);
    let one = b(4, Term::Zero, Term::Ones);
    let top = b(6, b(6, b(6, one, Term::Zero), Term::Zero), Term::Zero);
    let borrow = |t: &Term| -> Term {
        let Term::Op(LT, x, y) = t else { panic!("not an lt") };
        let (x, y) = ((**x).clone(), (**y).clone());
        b(2, b(1, not(x.clone()), y.clone()), b(1, not(b(3, x.clone(), y.clone())), b(4, x, y)))
    };
    let laws = [
        ("lt(0, xor(x, y))", "lt(and(0, y), sub(y, x))"),
        ("lt(add(x, x), x)", "lt(sub(-1, x), xor(x, 0))"),
        ("lt(add(x, y), -1)", "lt(xor(y, x), or(0, -1))"),
        ("lt(add(y, y), y)", "lt(sub(-1, y), and(y, y))"),
        ("lt(x, add(x, x))", "lt(or(0, x), sub(0, x))"),
        ("lt(x, xor(y, -1))", "lt(or(y, 0), xor(-1, x))"),
        ("lt(y, add(y, y))", "lt(xor(y, 0), sub(0, y))"),
    ];
    for (l, r) in laws {
        let (l, r) = (parse_term(l), parse_term(r));
        let fall = || MACHINE_FALLBACKS.with(|c| c.get());
        let before = fall();
        let direct = rewrite_law(4, 2, &l, &r).is_some();
        let direct_fell = fall() - before;
        let (bl, br) = (b(1, borrow(&l), top.clone()), b(1, borrow(&r), top.clone()));
        let before = fall();
        let via = rewrite_law(4, 2, &bl, &br).is_some();
        println!("BORROW {} = {}: lt form proved={direct} machine proofs {direct_fell}; borrow form proved={via} machine proofs {}", l.show(), r.show(), fall() - before);
    }
}

/// Soundness sweep (search note section 64). `SWEEP_FAMILY` (mul, shl, lt, shr; sized by the `RULEMINER_*` vars),
/// `SWEEP_WIDTHS` (default `3,4`). (A) Every law plausible at widths 1-6 that the rewriter proves is kernel-checked at each
/// width. (B) Every law equal at width 4 but false at some width `w` in 1..=6 must be refused at `w` (no proof, or a proof
/// the kernel rejects). Prints counts; panics on a failed check or an accepted false law.
#[test]
#[ignore]
pub fn soundness_sweep() {
    let _scope = tatic::kernel::InternScope::enter();
    println!("SWEEP machine at start: {}", machine_state());
    let family = std::env::var("SWEEP_FAMILY").unwrap_or_else(|_| "mul".into());
    let widths: Vec<usize> = std::env::var("SWEEP_WIDTHS").unwrap_or_else(|_| "3,4".into()).split(',').map(|w| w.parse().unwrap()).collect();
    let kv = family_vars(&family);
    let laws = family_laws(&family, &env_or::<usize>, 4, kv, env_or("MULMINER_MAX", 7) as u32);
    let capped = |t: &Term, w: usize| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap()) && w > 0;
    let (mut checked, mut unproved, mut refused, mut false_laws) = (0usize, 0usize, 0usize, 0usize);
    let t0 = Instant::now();
    for (name, t1, t2) in &laws {
        if capped(t1, 1) || capped(t2, 1) {
            continue;
        }
        let true_everywhere = (1..=6).all(|w| t1.plausibly_equals(t2, w, kv));
        if true_everywhere {
            for &w in &widths {
                match rewrite_law(w, kv, t1, t2) {
                    Some((p, s)) => {
                        if let Err(m) = check(&Ctx::new(), &p, &s) {
                            panic!("kernel rejected the proof of {name} at width {w}: {}", m.chars().take(300).collect::<String>());
                        }
                        checked += 1;
                    }
                    None => unproved += 1,
                }
            }
        } else {
            false_laws += 1;
            for w in (1..=6).filter(|w| !t1.plausibly_equals(t2, *w, kv)) {
                if let Some((p, s)) = rewrite_law(w, kv, t1, t2) {
                    assert!(check(&Ctx::new(), &p, &s).is_err(), "FALSE law accepted: {name} at width {w}");
                }
                refused += 1;
            }
        }
    }
    println!("SWEEP {family}: {} laws; true: {checked} proofs kernel-checked at widths {widths:?}, {unproved} unproved; false at some width: {false_laws} laws, {refused} (law, width) pairs refused; {:?}", laws.len(), t0.elapsed());
    println!("SWEEP machine at end: {}", machine_state());
}

/// Scaling probe (search note section 65): a sample of each family's laws (`SWEEP_SAMPLE`, default 30, evenly spaced among the
/// true laws within the carry cap) proved by `rewrite_law` and kernel-checked at each of `SWEEP_WIDTHS` (default `4,8,16,32`),
/// then every promoted rule via `prove_rule`. Per width: proofs, unproved, build and check seconds (sum and max), flushed as it goes.
#[test]
#[ignore]
pub fn scaling_sweep() {
    // SWEEP_SCOPE=law: one intern scope per law instead of one for the sweep (separates table size from per-node cost)
    let per_law = std::env::var("SWEEP_SCOPE").is_ok_and(|v| v == "law");
    let _scope = (!per_law).then(tatic::kernel::InternScope::enter);
    println!("SCALE machine at start: {}", machine_state());
    let family = std::env::var("SWEEP_FAMILY").unwrap_or_else(|_| "mul".into());
    let widths: Vec<usize> = std::env::var("SWEEP_WIDTHS").unwrap_or_else(|_| "4,8,16,32".into()).split(',').map(|w| w.parse().unwrap()).collect();
    let kv = family_vars(&family);
    if let Ok(f) = std::env::var("SWEEP_RULES") {
        let rules = parse_rules(&std::fs::read_to_string(f).unwrap());
        EXTRA_RULES.with(|e| *e.borrow_mut() = rules);
    }
    let all = family_laws(&family, &env_or::<usize>, 4, kv, env_or("MULMINER_MAX", 7) as u32);
    let ok: Vec<&(String, Term, Term)> = all
        .iter()
        .filter(|(_, a, b)| (1..=6).all(|w| a.plausibly_equals(b, w, kv)) && ![a, b].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap())))
        .collect();
    let sample = env_or("SWEEP_SAMPLE", 30).min(ok.len()).max(1);
    let picked: Vec<&&(String, Term, Term)> = (0..sample).map(|i| &ok[i * ok.len() / sample]).collect();
    for &w in &widths {
        let (mut proved, mut none, mut build, mut check_t, mut worst) = (0, 0, 0f64, 0f64, (0f64, String::new()));
        let mut dags: Vec<usize> = vec![];
        let fb0 = MACHINE_FALLBACKS.with(|c| c.get());
        for law in &picked {
            let (name, t1, t2) = &***law;
            let _law_scope = per_law.then(tatic::kernel::InternScope::enter);
            RULE_BUDGET.with(|b| b.set(200));
            let t = Instant::now();
            let r = rewrite_law(w, kv, t1, t2);
            let b = t.elapsed().as_secs_f64();
            build += b;
            match r {
                Some((p, s)) => {
                    dags.push(tatic::kernel::term_sizes(&p).0 as usize);
                    let t = Instant::now();
                    ck(name, &p, &s);
                    let c = t.elapsed().as_secs_f64();
                    check_t += c;
                    proved += 1;
                    if b + c > worst.0 {
                        worst = (b + c, name.clone());
                    }
                }
                None => none += 1,
            }
        }
        println!("SCALE {family} n={w}: {proved} proved, {none} unproved of {}; build {build:.1}s, check {check_t:.1}s, slowest {:.2}s ({}), {} machine proofs", picked.len(), worst.0, worst.1, MACHINE_FALLBACKS.with(|c| c.get()) - fb0);
        dags.sort();
        if let Some(m) = dags.get(dags.len() / 2) {
            println!("SCALE {family} n={w}: proof dag nodes: median {m}, max {}, total {}", dags[dags.len() - 1], dags.iter().sum::<usize>());
        }
    }
    let t = Instant::now();
    for &w in widths.iter().filter(|_| std::env::var("SWEEP_RULES").is_err()) {
        let t = Instant::now();
        for (l, r) in promoted_rules() {
            assert!(prove_rule(w, l.max_var().max(r.max_var()) + 1, l, r).is_some(), "promoted rule not provable at width {w}");
        }
        println!("SCALE promoted rules n={w}: {:.1}s for {}", t.elapsed().as_secs_f64(), promoted_rules().len());
    }
    let _ = t;
    println!("SCALE machine at end: {}", machine_state());
}

/// The pool of the `add3` family: terms over `x`, `y`, `z` with at most one sum or difference above depth-1 terms.
///
/// `deep`: also the sums and differences of two depth-1 terms built from `add`, `sub` and `xor` (about 2^15 more terms).
pub fn add3_pool(deep: bool) -> Vec<Term> {
    let leaves = leaves3();
    let d1 = depth1(&[ADD, AND, OR, XOR, SUB], false);
    let mut p = d1.clone();
    // one more level: a sum or difference of a depth-1 term and a leaf
    for o in [ADD, SUB] {
        for a in &d1 {
            for b in &leaves {
                p.push(mk(o, a, b));
            }
        }
    }
    if deep {
        let arith: Vec<Term> = d1.iter().filter(|t| matches!(t, Term::Op(ADD | XOR | SUB, ..))).cloned().collect();
        for o in [ADD, SUB] {
            for a in &arith {
                for b in &arith {
                    p.push(mk(o, a, b));
                }
            }
        }
    }
    p
}

/// The three-variable families, by name. `pool3` is the single place that maps one to its term pool; everything else (law selection,
/// `family_vars`, the shape-halves test) follows from it.
pub const THREE_VAR_FAMILIES: [&str; 5] = ["add3", "mix3", "sbo3", "cmp3", "cmp3d"];

/// The term pool of a three-variable family (`None` for any other family). add3: the add/sub/xor reassociation family (`RULEMINER_DEEP3=1`
/// for the deeper pool); mix3: bit-trick laws, arithmetic and bitwise operators and `shl1` mixed (section 73); sbo3: add, sub, and, or only,
/// a leaf on either side at every level; cmp3: `lt` of two small add/sub/shl1 terms (laws about comparisons); cmp3d: cmp3 with
/// reassociation redexes inside the comparison.
pub fn pool3(family: &str, env: &dyn Fn(&str, usize) -> usize) -> Option<Vec<Term>> {
    Some(match family {
        "add3" => add3_pool(env("RULEMINER_DEEP3", 0) == 1),
        "mix3" => depth2_pool(&[ADD, AND, OR, XOR, SUB], true, &[ADD]),
        "sbo3" => depth2_pool(&[ADD, SUB, AND, OR], false, &[ADD, SUB]),
        "cmp3" => cmp3_pool(false),
        "cmp3d" => cmp3_pool(true),
        _ => return None,
    })
}

/// Variables per law of a family: the three-variable families against the two-variable rest.
pub fn family_vars(family: &str) -> usize {
    if THREE_VAR_FAMILIES.contains(&family) { 3 } else { 2 }
}

/// Terms of the `cmp3` family: `lt` of two arithmetic terms (add, sub, `shl1` over three variables, depth one: an operator over two
/// leaves, `shl1` of a leaf, or a leaf), so each law is a statement about a comparison. `lt` is never nested under arithmetic: the
/// encoding types its result differently.
pub fn cmp3_pool(deep: bool) -> Vec<Term> {
    let op = mk;
    let d1 = depth1(&[ADD, SUB], true);
    if deep {
        // cmp3d: the right argument may also be a sum or difference of a variable-only depth-1 term and a variable, so a comparison
        // can contain a reassociation redex (cmp3d mixes the comparison and the add/sub structures)
        let vars: Vec<Term> = (0..3).map(Term::V).collect();
        let mut v1 = vars.clone();
        for o in [ADD, SUB] {
            for a in &vars {
                for b in &vars {
                    v1.push(op(o, a, b));
                }
            }
        }
        let mut e = d1.clone();
        for o in [ADD, SUB] {
            for a in &v1 {
                for b in &vars {
                    e.push(op(o, a, b));
                    e.push(op(o, b, a));
                }
            }
        }
        return d1.iter().flat_map(|a| e.iter().map(|b| op(LT, a, b)).collect::<Vec<_>>()).collect();
    }
    d1.iter().flat_map(|a| d1.iter().map(|b| op(LT, a, b)).collect::<Vec<_>>()).collect()
}

/// Terms of the depth-2 families (sbo3, mix3): the depth-1 terms, each of `ops` over a depth-1 term and a leaf (both orders), `shl1` of
/// each depth-1 term when `shl`, and each of `sums` over two depth-1 terms.
pub fn depth2_pool(ops: &[usize], shl: bool, sums: &[usize]) -> Vec<Term> {
    let leaves = leaves3();
    let d1 = depth1(ops, shl);
    let mut p = d1.clone();
    for &o in ops {
        for a in &d1 {
            for b in &leaves {
                p.push(mk(o, a, b));
                p.push(mk(o, b, a));
            }
        }
    }
    if shl {
        p.extend(d1.iter().map(|a| mk(SHL1, a, &Term::Zero)));
    }
    for &o in sums {
        for a in &d1 {
            for b in &d1 {
                p.push(mk(o, a, b));
            }
        }
    }
    p
}

/// `x`, `y`, `z`, `0` and `-1`.
fn leaves3() -> Vec<Term> {
    (0..3).map(Term::V).chain([Term::Zero, Term::Ones]).collect()
}

fn mk(o: usize, a: &Term, b: &Term) -> Term {
    Term::Op(o, Box::new(a.clone()), Box::new(b.clone()))
}

/// The depth-1 terms: the leaves, each of `ops` over two leaves, and, with `shl`, `shl1` of a leaf.
fn depth1(ops: &[usize], shl: bool) -> Vec<Term> {
    let leaves = leaves3();
    let mut d1 = leaves.clone();
    for &o in ops {
        for a in &leaves {
            for b in &leaves {
                d1.push(mk(o, a, b));
            }
        }
    }
    if shl {
        d1.extend(leaves.iter().map(|a| mk(SHL1, a, &Term::Zero)));
    }
    d1
}

/// Three-variable probe (benchmark with headroom): equal pairs of the depth-1 pool over `x`, `y`, `z`, proved by
/// `rewrite_law` at width 4, counting the ones that still need a whole-term machine proof.
#[test]
#[ignore]
pub fn three_var_probe() {
    let _scope = tatic::kernel::InternScope::enter();
    println!("PROBE3 machine at start: {}", machine_state());
    let pool = add3_pool(false);
    let conj = pool_conjectures(pool.clone(), 4, 3, 0);
    println!("PROBE3 pool {} terms, {} conjectures", pool.len(), conj.len());
    let (mut ok, mut straggler, mut unproved) = (0, 0, 0);
    for (a, b) in conj.iter().filter(|(a, b)| (0..3).all(|v| a.has_var(v) || b.has_var(v))) {
        if !(1..=6).all(|w| a.plausibly_equals(b, w, 3)) {
            continue;
        }
        let before = MACHINE_FALLBACKS.with(|c| c.get());
        match rewrite_law(4, 3, a, b) {
            Some(_) => {
                let fell = MACHINE_FALLBACKS.with(|c| c.get()) - before;
                ok += 1;
                if fell > 0 {
                    straggler += 1;
                    println!("PROBE3 straggler {} = {} ({fell})", a.show(), b.show());
                }
            }
            None => {
                unproved += 1;
                println!("PROBE3 unproved {} = {}", a.show(), b.show());
            }
        }
    }
    println!("PROBE3 {ok} proved ({straggler} with a machine proof), {unproved} unproved");
}

#[test]
pub fn tie_break_orients_reassociation_and_leaves_commutativity_permutative() {
    let t = |s: &str| parse_term(s);
    for (l, r) in [("sub(sub(x, y), z)", "sub(x, add(y, z))"), ("add(sub(x, y), z)", "sub(add(x, z), y)")] {
        let (l, r) = (t(l), t(r));
        assert!(!rule_order_ok(&l, &r) && rule_order_or_tie(&l, &r), "{} -> {}", l.show(), r.show());
        assert!(!rule_order_or_tie(&r, &l), "{} -> {} must not be oriented both ways", r.show(), l.show());
    }
    let (l, r) = (t("add(x, y)"), t("add(y, x)"));
    // commutativity is not oriented by the tie-break; it is permutative (instance-ordered), in both directions
    assert!(!tie_greater(&l, &r) && !tie_greater(&r, &l) && rule_permutative(&l, &r) && rule_permutative(&r, &l));
}

#[test]
pub fn permutative_rules_are_admitted_and_oriented_by_instance() {
    let t = |s: &str| parse_term(s);
    let (l, r) = (t("add(sub(x, y), z)"), t("add(sub(z, y), x)"));
    assert!(rule_permutative(&l, &r) && rule_order_or_tie(&l, &r));
    assert!(!rule_permutative(&t("sub(sub(x, y), z)"), &t("sub(x, add(y, z))")), "reassociation is oriented by the tie-break instead");
}

/// Debug aid: the normal forms of both sides of the laws in `NF_LAWS` (`lhs = rhs` per line) under the built-in rules plus
/// the `lhs -> rhs` rules in `NF_RULES`, three variables, width 4.
#[test]
#[ignore]
pub fn normal_forms() {
    let _scope = tatic::kernel::InternScope::enter();
    let rules: Vec<(Term, Term)> = parse_rules(&std::fs::read_to_string(std::env::var("NF_RULES").unwrap_or_default()).unwrap_or_default());
    EXTRA_RULES.with(|e| *e.borrow_mut() = rules);
    TRACE_RULES.store(std::env::var("NF_TRACE").is_ok(), std::sync::atomic::Ordering::Relaxed);
    RULE_BUDGET.with(|b| b.set(200));
    let (n, k) = (4, 3);
    let ops = ops_for(n);
    let goods: Vec<(Expr, Expr)> = (0..k).map(|i| (var((2 * k - 1 - i) as u32), var((k - 1 - i) as u32))).collect();
    for line in std::fs::read_to_string(std::env::var("NF_LAWS").unwrap()).unwrap().lines().filter(|l| l.contains(" = ")) {
        let (a, b) = line.split_once(" = ").unwrap();
        let (a, b) = (parse_term(a), parse_term(b));
        RULE_BUDGET.with(|c| c.set(200));
        let (na, nb) = (rewrite(&a, n, &ops, &goods).0, rewrite(&b, n, &ops, &goods).0);
        println!("NF {} | {} {}", na.show(), nb.show(), if na.show() == nb.show() { "SAME" } else { "DIFF" });
    }
}

/// The `shrnot` rule and the laws it closes: a shift of a bitwise not distributes over xor, so both sides reach the same
/// xor of shifted atoms without a whole-term machine proof.
#[test]
pub fn shrnot_rule_is_provable_and_closes_the_shr_not_laws() {
    let _scope = tatic::kernel::InternScope::enter();
    for n in [4usize, 8] {
        let (l, r) = shrnot_rule();
        let (p, s) = prove_rule(n, 1, &l, &r).expect("shrnot");
        ck(&format!("shrnot n={n}"), &p, &s);
    }
    for (a, b) in [
        ("shr1(sub(-1, xor(x, y)), 0)", "xor(shr1(y, 0), xor(shr1(-1, 0), shr1(x, 0)))"),
        ("shr1(xor(xor(x, y), -1), 0)", "shr1(xor(sub(-1, x), y), 0)"),
    ] {
        let before = MACHINE_FALLBACKS.with(|c| c.get());
        let (p, s) = rewrite_law(4, 2, &parse_term(a), &parse_term(b)).unwrap_or_else(|| panic!("{a} = {b}"));
        ck(a, &p, &s);
        assert_eq!(MACHINE_FALLBACKS.with(|c| c.get()), before, "{a} = {b} needed a machine proof");
    }
}

/// The setup of the rule-set check tests: the `CHECK_RULES` installed as extra rules, `CHECK_FAMILY`'s variable count, and the laws of
/// the family (sized by the `RULEMINER_*` vars) that are plausible at widths 1-6.
fn check_laws() -> (Vec<(Term, Term)>, usize, Vec<(String, Term, Term)>) {
    let family = std::env::var("CHECK_FAMILY").unwrap_or_else(|_| "add3".into());
    let rules = parse_rules(&std::fs::read_to_string(std::env::var("CHECK_RULES").unwrap()).unwrap());
    let kv = family_vars(&family);
    let laws = family_laws(&family, &env_or::<usize>, 4, kv, 7).into_iter().filter(|(_, t1, t2)| (1..=6).all(|w| t1.plausibly_equals(t2, w, kv))).collect();
    EXTRA_RULES.with(|e| *e.borrow_mut() = rules.clone());
    (rules, kv, laws)
}

/// Kernel check of a rule set (search note section 75): every law of `CHECK_FAMILY` (sized by the `RULEMINER_*` vars, as in
/// `rule_miner`) that `rewrite_law` proves under the built-in rules (less `ABLATE`) plus the rules in `CHECK_RULES` is
/// checked by the kernel at width 4; prints how many were proved, how many without a whole-term machine proof.
#[test]
#[ignore]
pub fn rule_set_kernel_check() {
    let _scope = tatic::kernel::InternScope::enter();
    let (_, kv, laws) = check_laws();
    let (mut proved, mut free, mut none) = (0, 0, 0);
    for (name, t1, t2) in &laws {
        RULE_BUDGET.with(|b| b.set(200));
        let before = MACHINE_FALLBACKS.with(|c| c.get());
        match rewrite_law(4, kv, t1, t2) {
            Some((p, s)) => {
                ck(name, &p, &s);
                proved += 1;
                free += (MACHINE_FALLBACKS.with(|c| c.get()) == before) as u32;
            }
            None => none += 1,
        }
    }
    println!("CHECKED {proved} laws kernel-checked ({free} with no whole-term machine proof), {none} not proved");
    // confluence on this law set: both sides of a law reach the same normal form (the check above counts machine-free proofs, which can also come from a middle term)
    let (ops, goods): (_, Vec<(Expr, Expr)>) = (ops_for(4), (0..kv).map(|i| (var((2 * kv - 1 - i) as u32), var((kv - 1 - i) as u32))).collect());
    let (mut same, mut total) = (0, 0);
    for (_, t1, t2) in &laws {
        RULE_BUDGET.with(|b| b.set(200));
        let n1 = rewrite(t1, 4, &ops, &goods).0.show();
        RULE_BUDGET.with(|b| b.set(200));
        let n2 = rewrite(t2, 4, &ops, &goods).0.show();
        total += 1;
        same += (n1 == n2) as u32;
    }
    println!("NFSAME {same} of {total} laws have equal normal forms on both sides");
}

/// Where the kernel's work goes under a rule set: like `rule_set_kernel_check` (same `CHECK_FAMILY`, `CHECK_RULES`, `RULEMINER_*` vars), but
/// reports, for the laws proved without a whole-term machine proof ("rules") and for those that needed one ("machine"), the count, the
/// time to build the proof, the time for the kernel to check it, and its size (unique nodes / nodes per occurrence); then the same
/// for the proofs of the rules themselves, which a conversion rule or a one-time admission would pay once.
#[test]
#[ignore]
pub fn proof_cost_split() {
    use std::time::{Duration, Instant};
    let _scope = tatic::kernel::InternScope::enter();
    let (rules, kv, laws) = check_laws();
    #[derive(Default)]
    struct Acc { n: u32, build: Duration, check: Duration, nodes: usize, occ: u128 }
    let mut acc = [Acc::default(), Acc::default()]; // [rules, machine]
    let mut none = 0;
    for (name, t1, t2) in &laws {
        RULE_BUDGET.with(|b| b.set(200));
        let before = MACHINE_FALLBACKS.with(|c| c.get());
        let t = Instant::now();
        let Some((p, s)) = rewrite_law(4, kv, t1, t2) else { none += 1; continue };
        let build = t.elapsed();
        let t = Instant::now();
        ck(name, &p, &s);
        let check = t.elapsed();
        let (nodes, occ) = tatic::kernel::term_sizes(&p);
        let a = &mut acc[(MACHINE_FALLBACKS.with(|c| c.get()) != before) as usize];
        (a.n, a.build, a.check, a.nodes, a.occ) = (a.n + 1, a.build + build, a.check + check, a.nodes + nodes, a.occ + occ);
    }
    let mut ra = Acc::default();
    for (l, r) in &rules {
        let k = l.max_var().max(r.max_var()) + 1;
        let t = Instant::now();
        let Some((p, ty)) = prove_rule(4, k, l, r) else { continue };
        let build = t.elapsed();
        let t = Instant::now();
        ck(&l.show(), &p, &ty);
        let check = t.elapsed();
        let (nodes, occ) = tatic::kernel::term_sizes(&p);
        (ra.n, ra.build, ra.check, ra.nodes, ra.occ) = (ra.n + 1, ra.build + build, ra.check + check, ra.nodes + nodes, ra.occ + occ);
    }
    for (what, a) in [("rules", &acc[0]), ("machine", &acc[1]), ("rule-proofs", &ra)] {
        println!("COST {what}: n={} build={:.1}ms check={:.1}ms nodes={} occurrences={}", a.n, a.build.as_secs_f64() * 1e3, a.check.as_secs_f64() * 1e3, a.nodes, a.occ);
    }
    println!("COST not-proved={none}");
}

/// Each rule of the promoted sets parses, is a true law at widths 1-4, and is proved (and kernel-checked) at width 4.
#[test]
pub fn promoted_rule_sets_are_proved() {
    let _scope = tatic::kernel::InternScope::enter();
    for text in [include_str!("../../scripts/data/add3_mm_rules.txt"), include_str!("../../scripts/data/mix3_mm_rules.txt"), include_str!("../../scripts/data/add3_nl_rules.txt"), include_str!("../../scripts/data/mix3_nl_rules.txt")] {
        let rs: Vec<(Term, Term)> = parse_rules(&text);
        assert!(rs.len() >= 7);
        for (l, r) in rs {
            let k = l.max_var().max(r.max_var()) + 1;
            assert!((1..=4).all(|w| l.plausibly_equals(&r, w, k)), "{} -> {}", l.show(), r.show());
            let (p, t) = prove_rule(4, k, &l, &r).unwrap_or_else(|| panic!("{} -> {} not provable", l.show(), r.show()));
            ck(&l.show(), &p, &t);
        }
    }
}

/// Constant folding: closed terms equal to 0, -1 or 1 normalize to `0`, `-1`, `sub(0, -1)`, with no machine proof.
#[test]
pub fn closed_terms_fold_to_constants() {
    let _scope = tatic::kernel::InternScope::enter();
    for (a, b) in [("sub(-1, add(-1, -1))", "sub(0, -1)"), ("sub(add(0, 0), -1)", "sub(0, -1)"), ("xor(-1, -1)", "0"), ("add(-1, add(-1, sub(0, -1)))", "-1")] {
        let (t1, t2) = (parse_term(a), parse_term(b));
        let before = MACHINE_FALLBACKS.with(|c| c.get());
        let (p, ty) = rewrite_law(4, 1, &t1, &t2).unwrap_or_else(|| panic!("{a} = {b} not proved"));
        ck(a, &p, &ty);
        assert_eq!(MACHINE_FALLBACKS.with(|c| c.get()), before, "{a} = {b} needed a machine proof");
    }
}
