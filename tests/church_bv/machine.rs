use super::*;

/// The value of an add-free bitwise term at one bit position, with its `GoodBool` witness, given the operand bits.
pub fn term_gb<G: Gates>(g: &G, tm: &Term, u: &[G::S]) -> G::S {
    match tm {
        Term::V(i) => u[*i].clone(),
        Term::Zero => g.konst(false),
        Term::Ones => g.konst(true),
        Term::Op(AND, a, b) => g.and(&term_gb(g, a, u), &term_gb(g, b, u)),
        Term::Op(OR, a, b) => g.or(&term_gb(g, a, u), &term_gb(g, b, u)),
        Term::Op(XOR, a, b) => g.xor(&term_gb(g, a, u), &term_gb(g, b, u)),
        Term::Op(..) => panic!("`add` inside a leaf"),
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Src {
    Leaf(usize),
    Node(usize),
}

/// A sum tree flattened in post-order: `nodes[i]` adds two sources; `root` is the last node, or the only leaf of
/// a bare add-free term (no carries).
pub struct Machine {
    pub leaves: Vec<Term>,
    /// `(left, right, op)`, `op` as in `Term::Op`: add (0) and sub (4) nodes carry a bit between positions, the
    /// bitwise ones (1..=3) combine their operands' bits at the same position.
    pub nodes: Vec<(Src, Src, usize)>,
    pub root: Src,
}

impl Machine {
    /// A description that determines the machine (for lemma cache keys).
    pub fn key(&self) -> String {
        format!("{}|{:?}|{:?}", self.leaves.iter().map(|l| l.show()).collect::<Vec<_>>().join(","), self.nodes, self.root)
    }

    /// Any term over variables and constants: the machine computes it one bit position at a time.
    pub fn parse(t: &Term) -> Option<Machine> {
        // equal subterms are one node (so a chain of delay cells serves every shift of the same operand)
        fn go(t: &Term, m: &mut Machine, seen: &mut std::collections::HashMap<String, Src>) -> Option<Src> {
            match t {
                Term::Op(o, a, b) => {
                    if *o == SHR1 {
                        return None; // a right shift reads a later position: not a left-to-right machine
                    }
                    let key = t.show();
                    if let Some(src) = seen.get(&key) {
                        return Some(*src);
                    }
                    let a = go(a, m, seen)?;
                    let b = if *o == SHL1 { a } else { go(b, m, seen)? };
                    m.nodes.push((a, b, *o));
                    let src = Src::Node(m.nodes.len() - 1);
                    seen.insert(key, src);
                    Some(src)
                }
                _ => {
                    m.leaves.push(t.clone());
                    Some(Src::Leaf(m.leaves.len() - 1))
                }
            }
        }
        let mut m = Machine { leaves: vec![], nodes: vec![], root: Src::Leaf(0) };
        m.root = go(t, &mut m, &mut Default::default())?;
        Some(m)
    }

    /// The number of carries: one per add or sub node.
    pub fn carries(&self) -> usize {
        self.nodes.iter().filter(|n| OP_INFO[n.2].carries).count()
    }

    /// Whether the root is `lt`: the result is the last carry after the final position, not a vector.
    pub fn last(&self) -> bool {
        matches!(self.root, Src::Node(i) if self.nodes[i].2 == 5)
    }

    /// One position: `(output bit, next carries)` from the operand bits `u` and the carries `s`.
    pub fn step<G: Gates>(&self, g: &G, u: &[G::S], s: &[G::S]) -> (G::S, Vec<G::S>) {
        let leaf: Vec<G::S> = self.leaves.iter().map(|l| term_gb(g, l, u)).collect();
        let (mut val, mut next): (Vec<G::S>, Vec<G::S>) = (vec![], vec![]);
        let ones = g.konst(true);
        for (a, b, o) in self.nodes.iter() {
            let src = |s: &Src| match s {
                Src::Leaf(j) => leaf[*j].clone(),
                Src::Node(j) => val[*j].clone(),
            };
            let (x, y) = (src(a), src(b));
            let v = match o {
                1 => g.and(&x, &y),
                2 => g.or(&x, &y),
                3 => g.xor(&x, &y),
                6 => {
                    // a delay cell: the output is last position's operand bit
                    next.push(x.clone());
                    s[next.len() - 1].clone()
                }
                _ => {
                    let c = &s[next.len()];
                    // a subtractor's borrow is maj(~a, b, s)
                    next.push(if *o >= 4 { g.maj(&g.xor(&x, &ones), &y, c) } else { g.maj(&x, &y, c) });
                    g.sum3(&x, &y, c)
                }
            };
            val.push(v);
        }
        let out = match self.root {
            Src::Leaf(j) => leaf[j].clone(),
            Src::Node(j) => val[j].clone(),
        };
        (out, next)
    }
}

pub struct Encoding {
    /// `phi[side][j][s]`, `s` the side's carries as a number (first carry most significant).
    pub phi: [Vec<Vec<bool>>; 2],
    /// `g[0]` output, `g[1 + j]` next `phi_j`, indexed by (the `k` operand bits, then the `m` phi values), first most significant.
    pub g: Vec<Vec<bool>>,
}

/// The number with bits `bits`, first most significant.
pub fn index_of(bits: &[bool]) -> usize {
    bits.iter().fold(0, |a, b| a * 2 + *b as usize)
}

/// Each machine's (out, next carries) on all assignments of (operand bits, carries), computed once by the kernel.
pub fn raw_table(mach: &Machine, k: usize, gops: &GoodOps) -> Vec<Vec<bool>> {
    let c = mach.carries();
    (0..1usize << (k + c))
        .map(|r| {
            let bitgb = |pos: usize| Gb { e: bit(r >> (k + c - 1 - pos) & 1 == 1), g: f() };
            let u: Vec<Gb> = (0..k).map(bitgb).collect();
            let s: Vec<Gb> = (k..k + c).map(bitgb).collect();
            let (o, next) = mach.step(gops, &u, &s);
            let out = !mach.last() && normalize(&o.e) == t();
            std::iter::once(out).chain(next.iter().map(|g| normalize(&g.e) == t())).collect()
        })
        .collect()
}

pub type Reach = [Vec<bool>; 2];

/// The carry vectors one machine can reach from all-false by some input sequence (a vector as `index_of` reads it).
pub fn reachable(raw: &[Vec<bool>]) -> Vec<bool> {
    let c = raw[0].len() - 1;
    let mut seen = vec![false; 1 << c];
    seen[0] = true;
    let mut stack = vec![0usize];
    while let Some(s) = stack.pop() {
        for u in 0..raw.len() >> c {
            let next = index_of(&raw[u << c | s][1..]);
            if !seen[next] {
                seen[next] = true;
                stack.push(next);
            }
        }
    }
    seen
}

/// The functions `g` for which both machines factor through the encodings `phi` (one set per side), if any.
pub fn try_encoding(raw: &[Vec<Vec<bool>>; 2], k: usize, phi: &[Vec<Vec<bool>>; 2], reach: Option<&Reach>) -> Option<Vec<Vec<bool>>> {
    let m = phi[0].len();
    let mut g: Vec<Vec<Option<bool>>> = vec![vec![None; 1 << (k + m)]; 1 + m];
    for side in 0..2 {
        let c = raw[side][0].len() - 1;
        let ph = |s: usize| -> Vec<bool> { phi[side].iter().map(|t| t[s]).collect() };
        for (r, row) in raw[side].iter().enumerate() {
            let (u, s) = (r >> c, r & ((1 << c) - 1));
            if reach.is_some_and(|rc| !rc[side][s]) {
                continue;
            }
            let key = u << m | index_of(&ph(s));
            for (j, v) in std::iter::once(row[0]).chain(ph(index_of(&row[1..]))).enumerate() {
                match g[j][key] {
                    Some(old) if old != v => return None,
                    _ => g[j][key] = Some(v),
                }
            }
        }
    }
    Some(g.into_iter().map(|t| t.into_iter().map(|v| v.unwrap_or(false)).collect()).collect())
}

/// The coarsest consistent encoding, by Moore partition refinement over the carry vectors of both machines (all of
/// them, or only the `reach`able ones): two vectors share a class iff no input sequence tells them apart (the same
/// outputs, and with a root `lt` the same final bit). The class number, in binary, is the phi value. `None` when the
/// two start states (all-false) differ, i.e. the terms differ at some width.
pub fn moore_encoding(m1: &Machine, m2: &Machine, k: usize, gops: &GoodOps, reach: Option<&Reach>) -> Option<Encoding> {
    let raw = [raw_table(m1, k, gops), raw_table(m2, k, gops)];
    let cs = [m1.carries(), m2.carries()];
    let last = m1.last();
    let live = |side: usize, s: usize| reach.is_none_or(|rc| rc[side][s]);
    // class[side][s]; unreachable vectors stay in class 0 and are never looked at
    let mut class: [Vec<usize>; 2] = [0, 1].map(|side| (0..1usize << cs[side]).map(|s| if last && live(side, s) { s & 1 } else { 0 }).collect());
    let mut count = 0;
    loop {
        let mut ids: std::collections::HashMap<Vec<(usize, bool, usize)>, usize> = Default::default();
        let mut next: [Vec<usize>; 2] = [vec![0; class[0].len()], vec![0; class[1].len()]];
        for side in 0..2 {
            for s in (0..1usize << cs[side]).filter(|s| live(side, *s)) {
                let sig: Vec<(usize, bool, usize)> = std::iter::once((class[side][s], false, 0))
                    .chain((0..1usize << k).map(|u| {
                        let row = &raw[side][u << cs[side] | s];
                        (usize::MAX, row[0], class[side][index_of(&row[1..])])
                    }))
                    .collect();
                let fresh = ids.len();
                next[side][s] = *ids.entry(sig).or_insert(fresh);
            }
        }
        let done = ids.len() == count;
        count = ids.len();
        class = next;
        if done {
            break;
        }
    }
    if class[0][0] != class[1][0] {
        return None;
    }
    let m = (count.max(2) - 1).ilog2() as usize + 1;
    let phi: [Vec<Vec<bool>>; 2] = [0, 1].map(|side| (0..m).map(|j| class[side].iter().map(|c| c >> (m - 1 - j) & 1 == 1).collect()).collect());
    try_encoding(&raw, k, &phi, reach).map(|g| Encoding { phi, g })
}

/// `Id(Bool0, a, b)` from `h : Id(Bool0, false, true)`, for any Boolean `a`, `b`: congruence of `\c. mux c a b`.
pub fn absurd_id(h: Expr, a: &Expr, b: &Expr) -> Expr {
    let bl = bool0();
    let fmap = lam(bl.clone(), mux(var(0), shift(a, 0, 1), shift(b, 0, 1)));
    let p = cong1(&bl, &bl, &fmap, f(), t(), h);
    sym(&bl, &app(fmap.clone(), f()), &app(fmap, t()), p)
}

/// Nanoseconds spent in `add_tree_law`'s encoding searches: [all-states hit, all-states miss, reachable retry].
pub static LEMMA_HITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static PROF: [std::sync::atomic::AtomicU64; 3] = [std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0), std::sync::atomic::AtomicU64::new(0)];

/// One line of machine state to print with every timing (LONG_RUNS.md): Defender real-time protection and total CPU
/// load over two seconds, read through PowerShell; "unavailable" off Windows.
pub fn machine_state() -> String {
    let script = r"'RTP=' + (Get-MpComputerStatus).RealTimeProtectionEnabled + ' CPU=' + [int](Get-Counter '\Processor(_Total)\% Processor Time' -SampleInterval 2 -MaxSamples 2).CounterSamples[-1].CookedValue + '%'";
    std::process::Command::new("powershell")
        .args(["-NoProfile", "-Command", script])
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map_or_else(|| "machine state unavailable".to_string(), |t| t.trim().to_string())
}

/// Prints the machine state (Defender, CPU load) when created and again when dropped, so a timing run records both ends.
pub struct MachineBanner(&'static str);
impl MachineBanner {
    pub fn start(tag: &'static str) -> Self {
        println!("{tag} machine at start: {}", machine_state());
        MachineBanner(tag)
    }
}
impl Drop for MachineBanner {
    fn drop(&mut self) {
        println!("{} machine at end: {}", self.0, machine_state());
    }
}

/// What `prove_checked` found for a law.
pub enum Verdict {
    /// proved by `add_tree_law` and accepted by the kernel
    Proved,
    /// no proof and a side is over the carry cap
    OverCap,
    /// no proof, and neither side has a carry (`bitwise_law` territory)
    CarryFree,
    /// no proof within the cap; `generic` = the law holds at widths 1..6 (else it is width-specific and cannot have one)
    NoProof { generic: bool },
}
/// A `Verdict` with the time `add_tree_law` took and the time the kernel took to check its proof.
pub struct Tried {
    pub verdict: Verdict,
    pub law: std::time::Duration,
    pub check: std::time::Duration,
}
/// The driver step shared by the conjecture miners: prove `t1 = t2` over `nv` variables at width `n`, kernel-check the proof, else classify the failure.
pub fn prove_checked(n: usize, nv: usize, name: &str, t1: &Term, t2: &Term) -> Tried {
    let t = Instant::now();
    let law = add_tree_law(n, nv, t1, t2);
    let law_time = t.elapsed();
    let verdict = match law {
        Some((p, s)) => {
            let t = Instant::now();
            ck(name, &p, &s);
            return Tried { verdict: Verdict::Proved, law: law_time, check: t.elapsed() };
        }
        None => {
            let carries = [t1, t2].map(|t| Machine::parse(t).map_or(0, |m| m.carries())).into_iter().max().unwrap_or(0);
            if carries > carry_cap() {
                Verdict::OverCap
            } else if carries == 0 {
                Verdict::CarryFree
            } else {
                Verdict::NoProof { generic: t1.is_law(t2, nv) }
            }
        }
    };
    Tried { verdict, law: law_time, check: std::time::Duration::ZERO }
}

/// The most carries per side `add_tree_law` takes on (unguarded lemmas are decision diagrams, guarded ones case trees over `k + carries` bits); env `CARRY_CAP`.
pub fn carry_cap() -> usize {
    env_or("CARRY_CAP", 10)
}

/// Proof of `t1 = t2` for two sum trees of add-free leaves over `k` good vectors, with a carry encoding: found by
/// `moore_encoding` (first over all carry states, then over the reachable ones); `None` when there is none.
pub fn add_tree_law(n: usize, k: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    if !t1.plausibly_equals(t2, n, k) {
        return None;
    }
    let (m1, m2) = (Machine::parse(t1)?, Machine::parse(t2)?);
    let last = m1.last();
    if last != m2.last() {
        return None;
    }
    let cs = [m1.carries(), m2.carries()];
    if cs[0].max(cs[1]) > carry_cap() {
        return None;
    }
    if cs[0] + cs[1] == 0 {
        return None;
    }
    let gops = GoodOps::new();
    let attempt = |reach: Option<&Reach>| {
        moore_encoding(&m1, &m2, k, &gops, reach)
    };
    // first over all carry states; failing that, over the reachable ones, with the lemmas conditional on an invariant
    let t_all = Instant::now();
    let first = attempt(None);
    PROF[if first.is_some() { 0 } else { 1 }].fetch_add(t_all.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
    let (enc, inv): (Encoding, Option<Reach>) = match first {
        Some(e) => (e, None),
        None => {
            // guarded lemmas are still case trees over k + c bits, so they keep the old cap
            if cs[0].max(cs[1]) > 6 {
                return None;
            }
            let t_reach = Instant::now();
            let r = [reachable(&raw_table(&m1, k, &gops)), reachable(&raw_table(&m2, k, &gops))];
            if r.iter().all(|v| v.iter().all(|x| *x)) {
                return None;
            }
            let second = attempt(Some(&r));
            PROF[2].fetch_add(t_reach.elapsed().as_nanos() as u64, std::sync::atomic::Ordering::Relaxed);
            (second?, Some(r))
        }
    };
    let m = enc.phi[0].len();
    // with a root `lt`: the final result as a function `dec` of the phi values
    let mut dec = vec![false; 1 << m];
    for side in 0..2 {
        for s in 0..1usize << cs[side] {
            if inv.as_ref().is_none_or(|r| r[side][s]) {
                dec[index_of(&(0..m).map(|j| enc.phi[side][j][s]).collect::<Vec<_>>())] = s & 1 == 1;
            }
        }
    }
    let machines = [m1, m2];
    let phi_expr = |side: usize, j: usize, s: &[Expr]| table_app(s, &|b| enc.phi[side][j][index_of(b)]);
    let g_expr = |j: usize, v: &[Expr]| table_app(v, &|b| enc.g[j][index_of(b)]);
    // F_j of a side at symbolic (operand bits, carries): j = 0 output, 1..=m the next phi values
    let side_f = |side: usize, j: usize, v: &[Expr]| -> Expr {
        let dummy: Vec<Gb> = v.iter().map(|e| Gb { e: e.clone(), g: f() }).collect();
        let (o, next) = machines[side].step(&gops, &dummy[..k], &dummy[k..]);
        match j {
            0 => o.e,
            _ => phi_expr(side, j - 1, &next.iter().map(|g| g.e.clone()).collect::<Vec<_>>()),
        }
    };
    // the same functions over diagram signals (F_j of a side, and G_j at the operand bits and the phi values)
    let phi_sig = |g: &DdGates, side: usize, j: usize, s: &[Sig]| g.table(s, &|b| enc.phi[side][j][index_of(b)]);
    let side_sig = |g: &DdGates, side: usize, j: usize, v: &[Sig]| -> Sig {
        let (o, next) = machines[side].step(g, &v[..k], &v[k..]);
        match j {
            0 => o,
            _ => phi_sig(g, side, j - 1, &next),
        }
    };
    let inv_expr = |side: usize, v: &[Expr]| table_app(v, &|b| inv.as_ref().unwrap()[side][index_of(b)]);
    // `Id(a, b)` for the `nv` bits `v` by case analysis; the carries are `v[off..]`. Over the reachable states only
    // (with `inv`), the lemma takes `Id(I(carries), true)` and the unreachable cases are absurd.
    // diagrams pay off only once the case tree is big (2^nv leaves); below that their per-node proofs cost more
    let dd_min: usize = env_or("DDMIN", 9);
    let use_dd = |nv: usize| inv.is_none() && std::env::var("NOBDD").is_err() && nv >= dd_min;
    let guarded = |side: usize, nv: usize, off: usize, tag: &str, ab: &dyn Fn(&[Expr]) -> (Expr, Expr), dd: DdBuild| -> Expr {
        let key = format!("{}|{k}|{nv}|{tag}|{:?}|{:?}", machines[side].key(), inv.as_ref().map(|r| &r[side]), enc.phi[side]);
        if let Some(e) = LEMMAS.with(|c| c.borrow().get(&key).cloned()) {
            LEMMA_HITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            return e;
        }
        let hty = |v: &[Expr]| id(bool0(), inv_expr(side, &v[off..]), t());
        if inv.is_some() && std::env::var("GUARDTRACE").is_ok() {
            eprintln!("GUARDED lemma nv={nv} tag={tag}");
        }
        if use_dd(nv)
            && let Some(e) = lemma_dd(nv, dd) {
                LEMMAS.with(|c| c.borrow_mut().insert(key, e.clone()));
                return e;
            }
        let e = lemma_n(
            nv,
            &|v| {
                let (a, b) = ab(v);
                let inner = id(bool0(), a, b);
                if inv.is_some() { pi(hty(v), shift(&inner, 0, 1)) } else { inner }
            },
            &|bits| {
                let lits: Vec<Expr> = bits.iter().map(|b| bit(*b)).collect();
                let (a, b) = ab(&lits);
                match &inv {
                    None => refl(a),
                    Some(r) => lam(hty(&lits), if r[side][index_of(&bits[off..])] { refl(a) } else { absurd_id(var(0), &a, &b) }),
                }
            },
        )
        .0;
        LEMMAS.with(|c| c.borrow_mut().insert(key, e.clone()));
        e
    };
    // lemmas Id(F_j, G_j(operand bits, phi(carries))) by case analysis on the k + c bits
    let lemmas: Vec<Vec<Expr>> = (0..2)
        .map(|side| {
            (0..=m)
                .map(|j| {
                    if last && j == 0 {
                        return t();
                    }
                    guarded(side, k + cs[side], k, &format!("F{j}|{:?}", enc.g[j]), &|v| {
                        let key: Vec<Expr> = v[..k].iter().cloned().chain((0..m).map(|q| phi_expr(side, q, &v[k..]))).collect();
                        (side_f(side, j, v), g_expr(j, &key))
                    }, &|g, v| {
                        let key: Vec<Sig> = v[..k].iter().cloned().chain((0..m).map(|q| phi_sig(g, side, q, &v[k..]))).collect();
                        (side_sig(g, side, j, v), g.table(&key, &|b| enc.g[j][index_of(b)]))
                    })
                })
                .collect()
        })
        .collect();
    // the invariant is preserved by a step
    let pres: Vec<Expr> = (0..2)
        .map(|side| {
            if inv.is_none() {
                return t();
            }
            guarded(side, k + cs[side], k, "P", &|v| {
                let dummy: Vec<Gb> = v.iter().map(|e| Gb { e: e.clone(), g: f() }).collect();
                let next = machines[side].step(&gops, &dummy[..k], &dummy[k..]).1;
                (inv_expr(side, &next.iter().map(|g| g.e.clone()).collect::<Vec<_>>()), t())
            }, &|_, v| (v[0].clone(), v[0].clone()))
        })
        .collect();
    let dec_expr = |v: &[Expr]| table_app(v, &|b| dec[index_of(b)]);
    // the last carry is a function of the phi values: Id(carry_last, dec(phi(carries))) by cases
    let dlemmas: Vec<Expr> = (0..2)
        .map(|side| {
            if !last {
                return t();
            }
            guarded(side, cs[side], 0, &format!("D|{dec:?}"), &|v| (v[cs[side] - 1].clone(), dec_expr(&(0..m).map(|q| phi_expr(side, q, v)).collect::<Vec<_>>())), &|g, v| {
                (v[cs[side] - 1].clone(), g.table(&(0..m).map(|q| phi_sig(g, side, q, v)).collect::<Vec<_>>(), &|b| dec[index_of(b)]))
            })
        })
        .collect();
    let core = |bits: VarBitFn, goods: VarBitFn| {
        let bl = bool0();
        let tr = |x: &Expr, y: &Expr, w: &Expr, p: Expr, q: Expr| trans_proof(&bl, x, y, w, p, q);
        let zero = Gb { e: f(), g: good_bit(false) };
        let mut st: Vec<Vec<Gb>> = (0..2).map(|side| vec![zero.clone(); cs[side]]).collect();
        // the initial phi values agree by evaluation (both are the constant false)
        let mut ip: Vec<Expr> = (0..m).map(|j| refl(phi_expr(0, j, &vec![f(); cs[0]]))).collect();
        // the invariant holds at the all-false state (it is reachable)
        let mut hy: Vec<Expr> = vec![refl(t()), refl(t())];
        let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
        for i in 0..n {
            let ug: Vec<Gb> = (0..k).map(|v| Gb { e: bits(v, i), g: goods(v, i) }).collect();
            let ub: Vec<Expr> = ug.iter().map(|g| g.e.clone()).collect();
            let sx = |side: usize| -> Vec<Expr> { st[side].iter().map(|g| g.e.clone()).collect() };
            let vs = |side: usize| -> Vec<Expr> { ub.iter().cloned().chain(sx(side)).collect() };
            let pq = |side: usize| -> Vec<Expr> { (0..m).map(|j| phi_expr(side, j, &sx(side))).collect() };
            let key = |p: &[Expr]| -> Vec<Expr> { ub.iter().cloned().chain(p.iter().cloned()).collect() };
            let eq = |j: usize| {
                let (fl, fr) = (side_f(0, j, &vs(0)), side_f(1, j, &vs(1)));
                let (pl, pr) = (pq(0), pq(1));
                let (gl, gr) = (g_expr(j, &key(&pl)), g_expr(j, &key(&pr)));
                let inst = |side: usize| {
                    let args = vs(side).into_iter().chain(ug.iter().map(|g| g.g.clone())).chain(st[side].iter().map(|g| g.g.clone()));
                    let mut args: Vec<Expr> = args.collect();
                    if inv.is_some() {
                        args.push(hy[side].clone());
                    }
                    apps(lemmas[side][j].clone(), args)
                };
                let mut fmap = g_expr(j, &ub.iter().map(|e| shift(e, 0, m as i32)).chain((0..m).map(|q| var((m - 1 - q) as u32))).collect::<Vec<_>>());
                for _ in 0..m {
                    fmap = lam(bl.clone(), fmap);
                }
                let link = cong_n(&bl, &bl, &fmap, &pl, &pr, ip.clone());
                let back = sym(&bl, &fr, &gr, inst(1));
                let mid = tr(&gl, &gr, &fr, link, back);
                (fl.clone(), fr.clone(), tr(&fl, &gl, &fr, inst(0), mid))
            };
            let first = last as usize;
            let proofs: Vec<(Expr, Expr, Expr)> = (first..=m).map(eq).collect();
            if !last {
                s1.push(proofs[0].0.clone());
                s2.push(proofs[0].1.clone());
                e.push(proofs[0].2.clone());
            }
            ip = proofs[1 - first..].iter().map(|p| p.2.clone()).collect();
            if inv.is_some() {
                for side in 0..2 {
                    let args = vs(side).into_iter().chain(ug.iter().map(|g| g.g.clone())).chain(st[side].iter().map(|g| g.g.clone())).chain([hy[side].clone()]);
                    hy[side] = apps(pres[side].clone(), args.collect());
                }
            }
            for side in 0..2 {
                st[side] = machines[side].step(&gops, &ug, &st[side]).1;
            }
        }
        (s1, s2, e, st, ip, hy)
    };
    if !last {
        return Some(k_var_law(n, k, t1, t2, &|bits, goods| {
            let (s1, s2, e, ..) = core(bits, goods);
            (s1, s2, e)
        }));
    }
    Some(k_var_law_to(n, k, &bv_ty(1), &|args| (t1.eval(&ops_for(n), n, args), t2.eval(&ops_for(n), n, args)), &|bits, goods| {
        let (.., st, ip, hy) = core(bits, goods);
        let bl = bool0();
        let sx = |side: usize| -> Vec<Expr> { st[side].iter().map(|g| g.e.clone()).collect() };
        let pq = |side: usize| -> Vec<Expr> { (0..m).map(|j| phi_expr(side, j, &sx(side))).collect() };
        let (pl, pr) = (pq(0), pq(1));
        let end = |side: usize| st[side][cs[side] - 1].e.clone();
        let inst = |side: usize| {
            let mut args: Vec<Expr> = sx(side).into_iter().chain(st[side].iter().map(|g| g.g.clone())).collect();
            if inv.is_some() {
                args.push(hy[side].clone());
            }
            apps(dlemmas[side].clone(), args)
        };
        let (dl, dr) = (dec_expr(&pl), dec_expr(&pr));
        let mut fmap = dec_expr(&(0..m).map(|q| var((m - 1 - q) as u32)).collect::<Vec<_>>());
        for _ in 0..m {
            fmap = lam(bl.clone(), fmap);
        }
        let link = cong_n(&bl, &bl, &fmap, &pl, &pr, ip);
        let back = sym(&bl, &end(1), &dr, inst(1));
        let mid = trans_proof(&bl, &dl, &dr, &end(1), link, back);
        let whole = trans_proof(&bl, &end(0), &dl, &end(1), inst(0), mid);
        let fbody = lam(bl.clone(), lam(sort(1), lam(karrow(1), app(var(0), var(2)))));
        cong_n(&bl, &bv_ty(1), &fbody, &[end(0)], &[end(1)], vec![whole])
    }))
}

#[test]
pub fn state_encoding_search_proves_three_leaf_sum_laws() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |a: Term, b: Term| Term::Op(ADD, Box::new(a), Box::new(b));
    for n in [1usize, 2, 4] {
        for (name, t1, t2) in [
            ("add (add x y) y = add x (add y y)", op(op(v(0), v(1)), v(1)), op(v(0), op(v(1), v(1)))),
            ("add (add y y) -1 = add y (add y -1)", op(op(v(1), v(1)), Term::Ones), op(v(1), op(v(1), Term::Ones))),
            ("add (add x -1) -1 = add x (add -1 -1)", op(op(v(0), Term::Ones), Term::Ones), op(v(0), op(Term::Ones, Term::Ones))),
        ] {
            if n == 1 {
                let e = moore_encoding(&Machine::parse(&t1).unwrap(), &Machine::parse(&t2).unwrap(), 2, &GoodOps::new(), None).unwrap();
                println!("ENCODING {name}: {} phi bits, phi1 {:?}", e.phi[0].len(), e.phi[0]);
            }
            let (p, s) = add_tree_law(n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no encoding"));
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        // a false law has no encoding
        assert!(add_tree_law(n, 2, &op(op(v(0), v(1)), v(1)), &op(v(0), op(v(0), v(0)))).is_none());
    }
}

#[test]
pub fn state_encoding_search_handles_bitwise_leaves_three_vectors_and_four_leaves() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let add = |a: Term, b: Term| op(0, a, b);
    for n in [1usize, 2, 4] {
        // x & y + x | y = x + y: the leaves are bitwise terms
        let t1 = add(op(1, v(0), v(1)), op(2, v(0), v(1)));
        let t2 = add(v(0), v(1));
        let (p, s) = add_tree_law(n, 2, &t1, &t2).expect("and+or");
        ck(&format!("and+or at n={n}"), &p, &s);
        // associativity over three vectors, found by search
        let (p, s) = add_tree_law(n, 3, &add(add(v(0), v(1)), v(2)), &add(v(0), add(v(1), v(2)))).expect("assoc3");
        ck(&format!("assoc over x y z at n={n}"), &p, &s);
        // four leaves (three carries, two-bit total carry): (((x+y)+z)+x) = (x+(y+(z+x)))
        let l = add(add(add(v(0), v(1)), v(2)), v(0));
        let r = add(v(0), add(v(1), add(v(2), v(0))));
        let (p, s) = add_tree_law(n, 3, &l, &r).expect("four leaves");
        ck(&format!("four leaves at n={n}"), &p, &s);
        // false laws have no encoding
        assert!(add_tree_law(n, 3, &l, &add(v(0), add(v(1), add(v(2), v(2))))).is_none());
        assert!(add_tree_law(n, 2, &t1, &add(v(0), v(0))).is_none());
    }
}

#[test]
pub fn symmetric_encoding_handles_unequal_carry_counts_bare_leaves_and_five_leaves() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let add = |a: Term, b: Term| op(0, a, b);
    for n in [1usize, 2, 4] {
        // one add against two: the zero leaf adds a carry that never fires
        let (p, s) = add_tree_law(n, 2, &add(v(1), Term::Ones), &add(Term::Ones, add(v(1), Term::Zero))).expect("unequal counts");
        ck(&format!("y + -1 = -1 + (y + 0) at n={n}"), &p, &s);
        // a bare leaf is a sum with no carries
        let (p, s) = add_tree_law(n, 2, &v(1), &add(v(1), Term::Zero)).expect("bare leaf");
        ck(&format!("y = y + 0 at n={n}"), &p, &s);
        let (p, s) = add_tree_law(n, 2, &op(3, v(0), Term::Ones), &add(op(3, v(0), Term::Ones), Term::Zero)).expect("bare bitwise leaf");
        ck(&format!("x^-1 = (x^-1) + 0 at n={n}"), &p, &s);
        assert!(add_tree_law(n, 2, &v(1), &add(v(1), Term::Ones)).is_none());
        // five leaves, four carries
        let l = add(add(add(add(v(0), v(1)), v(2)), v(0)), v(1));
        let r = add(v(0), add(v(1), add(v(2), add(v(0), v(1)))));
        let (p, s) = add_tree_law(n, 3, &l, &r).expect("five leaves");
        ck(&format!("five leaves at n={n}"), &p, &s);
        assert!(add_tree_law(n, 3, &l, &add(v(0), add(v(1), add(v(2), add(v(0), v(0)))))).is_none());
        assert!(add_tree_law(n, 2, &add(v(1), Term::Ones), &add(v(0), add(v(1), Term::Zero))).is_none());
    }
}

/// Build and check time of the carry-encoding proof by number of carries (n = 4, three operands).
#[test]
#[ignore]
pub fn tree_proof_cost_by_carries() {
    let v = |i: usize| Term::V(i);
    let add = |a: Term, b: Term| Term::Op(ADD, Box::new(a), Box::new(b));
    let leaves = [v(0), v(1), v(2), v(0), v(1), v(2), v(0)];
    for n in [4usize] {
        for c in 2..=6usize {
            let left = leaves[1..=c].iter().fold(leaves[0].clone(), |a, b| add(a, b.clone()));
            let right = leaves[..c].iter().rev().fold(leaves[c].clone(), |a, b| add(b.clone(), a));
            let _scope = tatic::kernel::InternScope::enter();
            let t0 = Instant::now();
            let (p, s) = add_tree_law(n, 3, &left, &right).expect("encoding");
            let built = t0.elapsed();
            let t1 = Instant::now();
            let ok = check(&Ctx::new(), &p, &s).is_ok();
            println!("TREECOST n={n} carries={c}: build {built:?}, check {:?}, ok {ok}", t1.elapsed());
        }
    }
}

#[test]
pub fn sub_computes_is_good_and_its_laws_are_found_by_the_encoding_search() {
    let _scope = tatic::kernel::InternScope::enter();
    // computes: a - b mod 2^n on all pairs at n = 3
    let n = 3;
    for a in 0..8u128 {
        for b in 0..8u128 {
            let e = app2(sub(n), lit(n, a), lit(n, b));
            assert_eq!(normalize(&e), normalize(&lit(n, a.wrapping_sub(b) & 7)), "{a} - {b}");
        }
    }
    let (p, s) = good_sub(2);
    ck("good_sub n=2", &p, &s);
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    for n in [1usize, 2, 4] {
        for (name, k, l, r) in [
            ("x - x = 0", 2, op(4, v(0), v(0)), Term::Zero),
            ("x - 0 = x", 2, op(4, v(0), Term::Zero), v(0)),
            ("(x + y) - y = x", 2, op(4, op(0, v(0), v(1)), v(1)), v(0)),
            ("(x - y) + y = x", 2, op(0, op(4, v(0), v(1)), v(1)), v(0)),
            ("(x - y) - z = x - (y + z)", 3, op(4, op(4, v(0), v(1)), v(2)), op(4, v(0), op(0, v(1), v(2)))),
            ("0 - x = ~(x + -1)", 2, op(4, Term::Zero, v(0)), op(3, op(0, v(0), Term::Ones), Term::Ones)),
            ("~(x + y) = ~x - y", 2, op(3, op(0, v(0), v(1)), Term::Ones), op(4, op(3, v(0), Term::Ones), v(1))),
            ("(x & y) + (x | y) = x + y, bitwise nodes inside the machine", 2, op(0, op(1, v(0), v(1)), op(2, v(0), v(1))), op(0, v(0), v(1))),
            ("x - (y - z) = (x - y) + z", 3, op(4, v(0), op(4, v(1), v(2))), op(0, op(4, v(0), v(1)), v(2))),
        ] {
            let (p, s) = add_tree_law(n, k, &l, &r).unwrap_or_else(|| panic!("{name}: no encoding"));
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        // false laws have none
        assert!(add_tree_law(n, 2, &op(4, v(0), v(1)), &op(4, v(1), v(0))).is_none());
        assert!(add_tree_law(n, 2, &op(4, v(0), v(1)), &op(0, v(0), v(1))).is_none() || n == 1);
    }
}

/// Time of the kernel evaluation of one machine on every (operand bits, carries) assignment.
#[test]
#[ignore]
pub fn raw_table_probe() {
    let v = |i: usize| Term::V(i);
    let add = |a: Term, b: Term| Term::Op(ADD, Box::new(a), Box::new(b));
    let leaves = [v(0), v(1), v(2), v(0), v(1), v(2)];
    let gops = GoodOps::new();
    for c in 2..=5usize {
        let left = leaves[1..=c].iter().fold(leaves[0].clone(), |a, b| add(a, b.clone()));
        let m = Machine::parse(&left).unwrap();
        let t0 = Instant::now();
        let raw = raw_table(&m, 3, &gops);
        println!("PROBE raw_table carries={c}: {} rows in {:?}", raw.len(), t0.elapsed());
    }
}

/// Check time of a case-analysis lemma whose body is the machine's output against itself (c = 3..5, k = 3).
#[test]
#[ignore]
pub fn machine_lemma_probe() {
    let v = |i: usize| Term::V(i);
    let add = |a: Term, b: Term| Term::Op(ADD, Box::new(a), Box::new(b));
    let leaves = [v(0), v(1), v(2), v(0), v(1), v(2)];
    let gops = GoodOps::new();
    for c in 3..=5usize {
        let _scope = std::env::var("NO_SCOPE").is_err().then(tatic::kernel::InternScope::enter);
        let left = leaves[1..=c].iter().fold(leaves[0].clone(), |a, b| add(a, b.clone()));
        let m = Machine::parse(&left).unwrap();
        for (what, pick) in [("out", 0usize), ("next carry 0", 1), ("table of next carries", 2)] {
            let f_of = |vv: &[Expr]| -> Expr {
                let dummy: Vec<Gb> = vv.iter().map(|e| Gb { e: e.clone(), g: f() }).collect();
                let (o, next) = m.step(&gops, &dummy[..3], &dummy[3..]);
                match pick {
                    0 => o.e,
                    1 => next[0].e.clone(),
                    _ => table_app(&next.iter().map(|g| g.e.clone()).collect::<Vec<_>>(), &|b| b.iter().filter(|x| **x).count() % 2 == 1),
                }
            };
            let (p, ty) = lemma_n(3 + c, &|vv| id(bool0(), f_of(vv), f_of(vv)), &|b| refl(f_of(&b.iter().map(|x| bit(*x)).collect::<Vec<_>>())));
            let t0 = Instant::now();
            let ok = check(&Ctx::new(), &p, &ty).is_ok();
            println!("PROBE carries={c} {what}: check {:?} ok {ok}", t0.elapsed());
        }
    }
}

/// Where the per-lemma time goes: the case split alone (trivial leaves) against a real machine lemma.
#[test]
#[ignore]
pub fn lemma_overhead_probe() {
    for vars in [5usize, 6, 7, 8] {
        let (p, ty) = lemma_n(vars, &|v| id(bool0(), v[0].clone(), v[0].clone()), &|b| refl(bit(b[0])));
        let t0 = Instant::now();
        let ok = check(&Ctx::new(), &p, &ty).is_ok();
        println!("PROBE trivial lemma over {vars} bits: check {:?} ok {ok}", t0.elapsed());
    }
}

/// Mine at width `MINER_N` (default 4) over `MINER_VARS` variables (default 2), `MINER_DEEP=1` for terms two
/// operators deep. Prints the classes, then tries every conjecture over x, y with the generic builder.
#[test]
#[ignore]
pub fn conjecture_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    let (n, nvars, deep) = (env_or("MINER_N", 4), env_or("MINER_VARS", 2), env_or("MINER_DEEP", 0) == 1);
    let ops = ops_for(n);
    let ts = terms(nvars, deep);
    let t0 = Instant::now();
    let mut classes: std::collections::BTreeMap<u64, Vec<usize>> = Default::default();
    let mut cache = NfCache::default();
    // all input tuples, or `MINER_SAMPLE` of them (a fixed pseudo-random subset plus the all-zero and all-one
    // tuples): a class may then hold a false equality, which no proof builder or kernel check will accept
    let total = 1u128 << (n * nvars);
    let sample = env_or("MINER_SAMPLE", 0) as u128;
    let tuples: Vec<u128> = if sample == 0 || sample >= total {
        (0..total).collect()
    } else {
        let mut x = 0x9e3779b97f4a7c15u128;
        let mut v = vec![0, total - 1];
        for _ in 0..sample {
            x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            v.push((x >> 40) % total);
        }
        v.sort();
        v.dedup();
        v
    };
    for (i, t) in ts.iter().enumerate() {
        classes.entry(fingerprint(t, &ops, n, &tuples, &mut cache)).or_default().push(i);
    }
    let conjectures: usize = classes.values().map(|c| c.len() - 1).sum();
    println!("MINER n={n} vars={nvars} deep={deep}: {} terms, {} classes, {conjectures} conjectures, run in {:?}", ts.len(), classes.len(), t0.elapsed());
    let show = std::env::var("MINER_SHOW").is_ok();
    // Every conjecture (class representative = shortest term) over x, y, by what can check it.
    let (mut by_builder, mut rejected, mut needs_add, mut needs_z, mut by_third) = (0, vec![], vec![], 0, (0usize, 0usize));
    let (mut by_rewrite, mut rewrite_bugs, mut by_chain, mut by_tree) = (0, vec![], 0, 0);
    let t1 = Instant::now();
    for c in classes.values().filter(|c| c.len() > 1) {
        let mut members: Vec<&Term> = c.iter().map(|&i| &ts[i]).collect();
        members.sort_by_key(|t| t.show().len());
        for other in &members[1..] {
            let law = format!("{} = {}", members[0].show(), other.show());
            if show {
                println!("  CONJ: {law}");
            }
            let k = (members[0].max_var().max(other.max_var()) + 1).max(2);
            if k > 2 {
                by_third.0 += 1;
            }
            if members[0].uses_add() || other.uses_add() {
                match rewrite_law(n, k, members[0], other) {
                    Some((p, s)) if k > 2 && check(&Ctx::new(), &p, &s).is_ok() => by_third.1 += 1,
                    _ if k > 2 => match add_tree_law(n, k, members[0], other) {
                        Some((p, s)) if check(&Ctx::new(), &p, &s).is_ok() => by_third.1 += 1,
                        _ => needs_z += 1,
                    },
                    Some((p, s)) if check(&Ctx::new(), &p, &s).is_ok() => by_rewrite += 1,
                    Some(_) => rewrite_bugs.push(law),
                    None => {
                        // the generic carry-chain builder, in either orientation
                        let chain = carry_chain_law(n, members[0], other).or_else(|| carry_chain_law(n, other, members[0]));
                        match chain {
                            Some((p, s)) if check(&Ctx::new(), &p, &s).is_ok() => by_chain += 1,
                            _ => match add_tree_law(n, 2, members[0], other) {
                                Some((p, s)) if check(&Ctx::new(), &p, &s).is_ok() => by_tree += 1,
                                _ => needs_add.push(law),
                            },
                        }
                    }
                }
            } else {
                let (p, s) = bitwise_law_k(n, k, members[0], other);
                if check(&Ctx::new(), &p, &s).is_ok() {
                    by_builder += 1;
                    by_third.1 += (k > 2) as usize;
                } else {
                    rejected.push(law);
                }
            }
        }
    }
    println!("MINER generic builder: {by_builder} proved, {} rejected {rejected:?}, in {:?}", rejected.len(), t1.elapsed());
    println!("MINER carry-chain builder: {by_chain} proved, state-encoding search: {by_tree} proved");
    println!("MINER rewrite: {by_rewrite} proved, {} failed to check {:?}", rewrite_bugs.len(), &rewrite_bugs[..rewrite_bugs.len().min(5)]);
    println!("MINER third variable: {} conjectures, {} proved, {needs_z} unproved", by_third.0, by_third.1);
    println!("MINER no builder: {} still need `add`", needs_add.len());
    for law in needs_add.iter().take(12) {
        println!("  needs add: {law}");
    }
    // Known library lemmas: does the miner conjecture them, and does the template proof check?
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let same = |a: &Term, b: &Term| {
        classes.values().any(|c| c.iter().any(|&i| ts[i].show() == a.show()) && c.iter().any(|&i| ts[i].show() == b.show()))
    };
    let (p0, s0) = add_zero_proof(n, 0);
    let (p1, s1) = add_identity_proof(n, 0, true);
    let (p2, s2) = add_comm_proof(n, false);
    for (name, mined, proved) in [
        ("add x 0 = x", same(&op(0, v(0), Term::Zero), &v(0)), check(&Ctx::new(), &p0, &s0).is_ok()),
        ("add 0 x = x", same(&op(0, Term::Zero, v(0)), &v(0)), check(&Ctx::new(), &p1, &s1).is_ok()),
        ("add x y = add y x", same(&op(0, v(0), v(1)), &op(0, v(1), v(0))), check(&Ctx::new(), &p2, &s2).is_ok()),
    ] {
        println!("MINER known lemma {name}: conjectured {mined}, template proof checks {proved}");
        assert!(mined && proved, "{name}");
    }
    if deep && nvars >= 3 {
        let assoc = same(&op(0, op(0, v(0), v(1)), v(2)), &op(0, v(0), op(0, v(1), v(2))));
        println!("MINER add associativity conjectured: {assoc}");
    }
}

// ---- Comparison (search note section 20): `lt a b` is the final borrow of the chain for `a - b`, a `Bool0` result.

/// The terms `lt` is mined over: the leaves and every operator applied to two leaves.
/// The conjectures of a term pool: terms with equal values on every width-`n` tuple of `nv` variables are paired with
/// the group's first member, sorted for a stable order and, when `cap` is nonzero, sampled by stride down to about `cap`.
/// Behaviour signatures: a term's value on every input (n-bit values of nv variables, one byte each). Pool terms share subterms,
/// so each distinct subterm is evaluated once and its parent combines its children's vectors.
pub struct SigMemo {
    n: usize,
    mask: u128,
    inputs: usize,
    ids: std::collections::HashMap<(usize, usize, usize), usize>,
    sigs: Vec<Vec<u8>>,
}

impl SigMemo {
    pub fn new(n: usize, nv: usize) -> SigMemo {
        assert!(n <= 8, "behaviour signatures hold one byte per input");
        SigMemo { n, mask: low_bits(n), inputs: 1usize << (n * nv), ids: Default::default(), sigs: vec![] }
    }

    /// The id of `t`'s signature; equal ids mean equal behaviour on every input.
    pub fn id(&mut self, t: &Term) -> usize {
        let key = match t {
            Term::V(v) => (usize::MAX, *v, 0),
            Term::Zero => (usize::MAX - 1, 0, 0),
            Term::Ones => (usize::MAX - 2, 0, 0),
            Term::Op(o, a, b) => (*o, self.id(a), self.id(b)),
        };
        if let Some(&id) = self.ids.get(&key) {
            return id;
        }
        let (n, mask) = (self.n, self.mask);
        let sig: Vec<u8> = match t {
            Term::V(v) => (0..self.inputs).map(|i| (i >> (n * v) & mask as usize) as u8).collect(),
            Term::Zero => vec![0; self.inputs],
            Term::Ones => vec![mask as u8; self.inputs],
            Term::Op(o, ..) => (0..self.inputs).map(|i| (OP_INFO[*o].word)(self.sigs[key.1][i] as u128, self.sigs[key.2][i] as u128, mask) as u8).collect(),
        };
        self.sigs.push(sig);
        self.ids.insert(key, self.sigs.len() - 1);
        self.sigs.len() - 1
    }

    pub fn sig(&mut self, t: &Term) -> &[u8] {
        let id = self.id(t);
        &self.sigs[id]
    }
}

pub fn pool_conjectures(pool: impl IntoIterator<Item = Term>, n: usize, nv: usize, cap: usize) -> Vec<(Term, Term)> {
    let mut memo = SigMemo::new(n, nv);
    let mut groups: std::collections::HashMap<Vec<u8>, Vec<Term>> = Default::default();
    for t in pool {
        groups.entry(memo.sig(&t).to_vec()).or_default().push(t);
    }
    let mut conj: Vec<(Term, Term)> = groups.values().filter(|g| g.len() > 1).flat_map(|g| g[1..].iter().map(|t2| (g[0].clone(), t2.clone()))).collect();
    conj.sort_by_cached_key(|(a, b)| (a.show(), b.show()));
    if cap > 0 && conj.len() > cap {
        let stride = conj.len() / cap;
        conj = conj.into_iter().step_by(stride).take(cap).collect();
    }
    conj
}

pub fn lt_pool(nvars: usize) -> Vec<Term> {
    let mut leaves: Vec<Term> = (0..nvars).map(Term::V).collect();
    leaves.extend([Term::Zero, Term::Ones]);
    let mut pool = leaves.clone();
    for o in 0..5 {
        for a in &leaves {
            for b in &leaves {
                pool.push(Term::Op(o, Box::new(a.clone()), Box::new(b.clone())));
            }
        }
    }
    pool
}

#[test]
pub fn lt_computes_and_its_laws_are_found_by_the_encoding_search() {
    let _scope = tatic::kernel::InternScope::enter();
    let n = 4usize;
    // `lt_u` computes `a < b`
    let ops = ops_for(n);
    for (a, b) in [(0u128, 0u128), (3, 5), (5, 3), (7, 7), (0, 15), (15, 0), (8, 9)] {
        let e = app2(ops[5].clone(), lit(n, a), lit(n, b));
        assert_eq!(normalize(&e), normalize(&lit(1, (a < b) as u128)), "lt {a} {b}");
    }
    let v = |i: usize| Box::new(Term::V(i));
    let lt = |a: Term, b: Term| Term::Op(LT, Box::new(a), Box::new(b));
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    // lt x x = lt y y; and an operand-order law with a carry on both sides
    let laws = [
        ("lt x x = lt y y", lt(Term::V(0), Term::V(0)), lt(Term::V(1), Term::V(1))),
        ("lt (and x y) (or x y) = lt (and y x) (or y x)", lt(op(1, *v(0), *v(1)), op(2, *v(0), *v(1))), lt(op(1, *v(1), *v(0)), op(2, *v(1), *v(0)))),
    ];
    for (name, t1, t2) in &laws {
        let (p, s) = add_tree_law(n, 2, t1, t2).unwrap_or_else(|| panic!("no proof: {name}"));
        ck(name, &p, &s);
    }
    // these hold only on the reachable carry states (the borrow of `x - 0` never becomes 1, the borrow of `x + y < x`
    // equals the add's carry): proved with lemmas conditional on a reachability invariant
    for (name, t1, t2) in [
        ("lt x 0 = lt y 0", lt(Term::V(0), Term::Zero), lt(Term::V(1), Term::Zero)),
        ("lt (x+y) x = lt (x+y) y", lt(op(0, *v(0), *v(1)), Term::V(0)), lt(op(0, *v(0), *v(1)), Term::V(1))),
    ] {
        let (p, s) = add_tree_law(n, 2, &t1, &t2).unwrap_or_else(|| panic!("no proof: {name}"));
        ck(name, &p, &s);
    }
    // false laws are not proved: by the plausibility screen, and a wrong proof would not check
    assert!(add_tree_law(n, 2, &lt(Term::V(0), Term::V(1)), &lt(Term::V(1), Term::V(0))).is_none());
    assert!(add_tree_law(n, 2, &lt(Term::V(0), Term::V(1)), &lt(Term::V(0), op(0, *v(1), Term::Ones))).is_none());
}

/// All `lt` pairs over the pool that agree on every width-4 input, grouped by behaviour; each conjecture is
/// built and kernel-checked.
#[test]
#[ignore]
pub fn lt_conjecture_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    let _banner = MachineBanner::start("LTMINER");
    let n = 4usize;
    let nv = env_or("LTMINER_VARS", 2);
    let cap = env_or("LTMINER_MAX", 0);
    let pool = lt_pool(nv);
    let (mut total, mut proved, mut none) = (0, 0, 0);
    let t0 = Instant::now();
    let (mut t_law, mut t_ck) = (std::time::Duration::ZERO, std::time::Duration::ZERO);
    let conj = pool_conjectures(pool.iter().flat_map(|a| pool.iter().map(move |b| Term::Op(LT, Box::new(a.clone()), Box::new(b.clone())))), n, nv, cap);
    {
        for (g0, t2) in &conj {
            let g = [g0.clone()];
            total += 1;
            let tried = prove_checked(n, nv, &format!("{} = {}", g[0].show(), t2.show()), &g[0], t2);
            t_law += tried.law;
            t_ck += tried.check;
            match tried.verdict {
                Verdict::Proved => proved += 1,
                _ => {
                    none += 1;
                    // the groups are by behaviour at width 4; a law that fails at another width cannot have a proof for all widths
                    let why = match g[0].refute(t2, nv) {
                        None => "holds at widths 1..6".to_string(),
                        Some((w, vals)) => format!("width-specific, differs at width {w} on {vals:?}"),
                    };
                    println!("LTMINER no proof ({why}): {} = {}", g[0].show(), t2.show());
                }
            }
        }
    }
    let pf = |i: usize| std::time::Duration::from_nanos(PROF[i].load(std::sync::atomic::Ordering::Relaxed));
    println!("LTMINER time: add_tree_law {t_law:?} (all-states search: hit {:?}, miss {:?}; reachable retry {:?}), kernel check {t_ck:?}, lemma cache hits {}", pf(0), pf(1), pf(2), LEMMA_HITS.load(std::sync::atomic::Ordering::Relaxed));
    println!("LTMINER {total} conjectures, {proved} proved, {none} without a proof, {:?}", t0.elapsed());
}

// ---- Constant shifts (search note section 20). A shift reads another position, so it is not a carry machine; it
// is a rewiring of leaves. Laws over bitwise terms with constant shifts are proved per position: each position's
// equality is case analysis over the (variable, source position) bits it reads.

/// `x << k` (`left`) or `x >> k` as a vector operation: output bit `i` is input bit `i - k` (or `i + k`), else false.
pub fn shift_bv(n: usize, k: usize, left: bool) -> Expr {
    let d = 3 + n; // depth at the innermost body: a C kk a0..
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let outs: Vec<Expr> = (0..n).map(|i| shift_src(n, k, left, i).map_or_else(f, |j| v(3 + j))).collect();
    let mut body = apps(v(2), outs);
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    lam(bv_ty(n), lam(sort(1), lam(karrow(n), app2(var(2), var(1), body))))
}

/// The input position that output position `i` of a shift reads, if any.
pub fn shift_src(n: usize, k: usize, left: bool, i: usize) -> Option<usize> {
    if left { i.checked_sub(k) } else { Some(i + k).filter(|j| *j < n) }
}

pub type BitOp = fn(Expr, Expr) -> Expr;
pub const BIT_OPS: [BitOp; 3] = [and, or, xor];

/// Terms whose bit at a position reads bits of the variables at (possibly other) positions: the interface of `pos_law`.
pub trait PosTerm {
    fn pos_eval(&self, n: usize, vals: &[Expr]) -> Expr;
    fn pos_atoms(&self, n: usize, i: usize, out: &mut Vec<(usize, usize)>);
    fn pos_bit(&self, n: usize, i: usize, bit: &dyn Fn(usize, usize) -> Expr) -> Expr;
}
/// `Term`s without add/sub/lt: bitwise operators and the one-bit shifts.
impl PosTerm for Term {
    fn pos_eval(&self, n: usize, vals: &[Expr]) -> Expr {
        self.eval(&ops_for(n), n, vals)
    }
    fn pos_atoms(&self, n: usize, i: usize, out: &mut Vec<(usize, usize)>) {
        match self {
            Term::V(v) => out.push((*v, i)),
            Term::Zero | Term::Ones => {}
            Term::Op(SHL1, a, _) => {
                if let Some(j) = i.checked_sub(1) {
                    a.pos_atoms(n, j, out);
                }
            }
            Term::Op(SHR1, a, _) => {
                if i + 1 < n {
                    a.pos_atoms(n, i + 1, out);
                }
            }
            Term::Op(_, a, b) => {
                a.pos_atoms(n, i, out);
                b.pos_atoms(n, i, out);
            }
        }
    }
    fn pos_bit(&self, n: usize, i: usize, bit: &dyn Fn(usize, usize) -> Expr) -> Expr {
        match self {
            Term::V(v) => bit(*v, i),
            Term::Zero => f(),
            Term::Ones => t(),
            Term::Op(SHL1, a, _) => i.checked_sub(1).map_or_else(f, |j| a.pos_bit(n, j, bit)),
            Term::Op(SHR1, a, _) => {
                if i + 1 < n { a.pos_bit(n, i + 1, bit) } else { f() }
            }
            Term::Op(o @ 1..=3, a, b) => BIT_OPS[*o - 1](a.pos_bit(n, i, bit), b.pos_bit(n, i, bit)),
            Term::Op(o, ..) => panic!("{} is not bitwise or a shift", OP_INFO[*o].name),
        }
    }
}

/// Proof of `t1 = t2` over `k` good vectors: per position, case analysis over the bits both sides read.
pub fn pos_law<T: PosTerm>(n: usize, k: usize, t1: &T, t2: &T) -> (Expr, Expr) {
    let sides = |args: &[Expr]| (t1.pos_eval(n, args), t2.pos_eval(n, args));
    k_var_law_to(n, k, &bv_ty(n), &sides, &|bits, goods| {
        let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
        for i in 0..n {
            let mut atoms = vec![];
            t1.pos_atoms(n, i, &mut atoms);
            t2.pos_atoms(n, i, &mut atoms);
            atoms.sort();
            atoms.dedup();
            let at = |vals: &[Expr]| {
                let lookup = |v: usize, j: usize| vals[atoms.iter().position(|a| *a == (v, j)).unwrap()].clone();
                (t1.pos_bit(n, i, &lookup), t2.pos_bit(n, i, &lookup))
            };
            let (lemma, _) = lemma_n(
                atoms.len(),
                &|vals| {
                    let (a, b) = at(vals);
                    id(bool0(), a, b)
                },
                &|bs| refl(at(&bs.iter().map(|b| bit(*b)).collect::<Vec<_>>()).0),
            );
            let bit_vars: Vec<Expr> = atoms.iter().map(|(v, j)| bits(*v, *j)).collect();
            let args: Vec<Expr> = bit_vars.iter().cloned().chain(atoms.iter().map(|(v, j)| goods(*v, *j))).collect();
            let (a, b) = at(&bit_vars);
            s1.push(a);
            s2.push(b);
            e.push(apps(lemma, args));
        }
        let fbody = bits_to_bv(n);
        cong_n(&bool0(), &bv_ty(n), &fbody, &s1, &s2, e)
    })
}

/// `x << k` or `x >> k` as `k` one-bit shifts.
pub fn shift_k(k: usize, left: bool, a: Term) -> Term {
    (0..k).fold(a, |acc, _| Term::Op(if left { 6 } else { 7 }, Box::new(acc), Box::new(Term::Zero)))
}

#[test]
pub fn shift_ops_compute_and_shift_laws_check_and_false_ones_fail() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let sh = shift_k;
    let bw = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    for n in [1usize, 2, 4] {
        // the Church shifts compute
        for x in 0..1u128 << n {
            for (k, left) in [(0usize, true), (1, true), (2, false), (3, true)] {
                let want = if left { (x << k) & ((1 << n) - 1) } else { x >> k };
                assert_eq!(normalize(&app(shift_bv(n, k, left), lit(n, x))), normalize(&lit(n, want)), "n={n} x={x} k={k} left={left}");
            }
        }
        let laws = [
            ("shl1 (and x y) = and (shl1 x) (shl1 y)", sh(1, true, bw(1, v(0), v(1))), bw(1, sh(1, true, v(0)), sh(1, true, v(1)))),
            ("shr1 (or x y) = or (shr1 x) (shr1 y)", sh(1, false, bw(2, v(0), v(1))), bw(2, sh(1, false, v(0)), sh(1, false, v(1)))),
            ("shr1 (shl1 x) = and x (shr1 (shl1 -1))", sh(1, false, sh(1, true, v(0))), bw(1, v(0), sh(1, false, sh(1, true, Term::Ones)))),
            ("xor (shl1 x) (shl1 x) = 0", bw(3, sh(1, true, v(0)), sh(1, true, v(0))), Term::Zero),
            ("shl0 x = x", sh(0, true, v(0)), v(0)),
            ("shl n x = 0", sh(n, true, v(0)), Term::Zero),
            ("shr n x = 0", sh(n, false, v(0)), Term::Zero),
        ];
        for (name, t1, t2) in &laws {
            let (p, s) = bitwise_law_k(n, 2, t1, t2);
            ck(&format!("{name}, n={n}"), &p, &s);
        }
        // false laws do not check (skipped when the two sides happen to agree at this width)
        for (t1, t2) in [(sh(1, true, v(0)), v(0)), (sh(1, true, v(0)), sh(1, false, v(0))), (sh(1, false, sh(1, true, v(0))), v(0))] {
            if (0..1u128 << n).all(|x| t1.interp(n, &[x, 0]) == t2.interp(n, &[x, 0])) {
                continue;
            }
            let (p, s) = bitwise_law_k(n, 2, &t1, &t2);
            assert!(check(&Ctx::new(), &p, &s).is_err(), "false law checked: {} = {}, n={n}", t1.show(), t2.show());
        }
    }
}

/// Every pair of bitwise and shift terms over the pool that agree on all width-4 inputs, grouped by behaviour; each
/// conjecture is built and kernel-checked.
#[test]
#[ignore]
pub fn shift_conjecture_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    let n = 4usize;
    let leaves = [Term::V(0), Term::V(1), Term::Zero, Term::Ones];
    let mut base: Vec<Term> = leaves.to_vec();
    for a in &leaves {
        for (k, left) in [(1, true), (2, true), (1, false), (2, false)] {
            base.push(shift_k(k, left, a.clone()));
        }
    }
    let mut pool = base.clone();
    for o in 1..=3 {
        for a in &base {
            for b in &base {
                pool.push(Term::Op(o, Box::new(a.clone()), Box::new(b.clone())));
            }
        }
    }
    let level1: Vec<Term> = pool[base.len()..].to_vec();
    for a in &level1 {
        for (k, left) in [(1, true), (1, false), (2, true)] {
            pool.push(shift_k(k, left, a.clone()));
        }
    }
    let t0 = Instant::now();
    let conj = pool_conjectures(pool.iter().cloned(), n, 2, 0);
    for (a, b) in &conj {
        let (p, s) = bitwise_law_k(n, 2, a, b);
        ck(&format!("{} = {}", a.show(), b.show()), &p, &s);
    }
    println!("SHIFTMINER {} terms, {} conjectures proved and checked, 0 rejected, {:?}", pool.len(), conj.len(), t0.elapsed());
}

#[test]
pub fn shared_subterms_are_generalized_so_large_sums_stay_provable() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let add = |a: Term, b: Term| Term::Op(ADD, Box::new(a), Box::new(b));
    let s = add(add(v(0), v(1)), v(2)); // two carries
    // 8 carries on each side before sharing equal subterms (6 after), so `rewrite_law` generalizes S to a variable
    let t1 = add(s.clone(), add(s.clone(), s.clone()));
    let t2 = add(add(s.clone(), s.clone()), s.clone());
    let (p, st) = rewrite_law(2, 3, &t1, &t2).expect("generalized");
    ck("add S (add S S) = add (add S S) S", &p, &st);
    // not equal: no proof
    assert!(rewrite_law(2, 3, &t1, &add(add(s.clone(), s.clone()), v(0))).is_none());
}

// ---- Left shifts inside machines (search note section 21): `shl1 a` is a delay cell, a carry whose next value is
// the operand's bit and whose output is the previous one, so sums with shifts are ordinary machines.

#[test]
pub fn shifts_inside_sums_are_machines_and_their_laws_check() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let shl = |a: Term| op(6, a, Term::Zero);
    let n = 4usize;
    let laws = [
        ("shl1 x = add x x", shl(v(0)), op(0, v(0), v(0))),
        ("shl1 (add x y) = add (shl1 x) (shl1 y)", shl(op(0, v(0), v(1))), op(0, shl(v(0)), shl(v(1)))),
        ("shl1 (sub x y) = sub (shl1 x) (shl1 y)", shl(op(4, v(0), v(1))), op(4, shl(v(0)), shl(v(1)))),
        ("shl1 (shl1 x) = add (add x x) (add x x)", shl(shl(v(0))), op(0, op(0, v(0), v(0)), op(0, v(0), v(0)))),
        ("add x (shl1 x) = add (shl1 x) x", op(0, v(0), shl(v(0))), op(0, shl(v(0)), v(0))),
        ("add (shl1 x) y = add y (shl1 x)", op(0, shl(v(0)), v(1)), op(0, v(1), shl(v(0)))),
        ("shl1 (xor x y) = xor (shl1 x) (shl1 y)", shl(op(3, v(0), v(1))), op(3, shl(v(0)), shl(v(1)))),
    ];
    for (name, t1, t2) in &laws {
        let (p, s) = add_tree_law(n, 2, t1, t2).unwrap_or_else(|| panic!("no proof: {name}"));
        ck(name, &p, &s);
    }
    // false laws get no proof
    assert!(add_tree_law(n, 2, &shl(v(0)), &v(0)).is_none());
    assert!(add_tree_law(n, 2, &shl(v(0)), &op(0, v(0), v(1))).is_none());
}

/// The equal pairs of the `shl1` pool over `nv` variables at width 4 (leaves, shifted leaves, every operator on two of
/// them, and shifts of those), each group's first term paired with the others.
pub fn shl_conjectures(nv: usize) -> Vec<(Term, Term)> {
    let n = 4usize;
    let b = |o: usize, a: &Term, c: &Term| Term::Op(o, Box::new(a.clone()), Box::new(c.clone()));
    let shl = |a: &Term| b(6, a, &Term::Zero);
    let leaves: Vec<Term> = (0..nv).map(Term::V).chain([Term::Zero, Term::Ones]).collect();
    let mut base: Vec<Term> = leaves.to_vec();
    base.extend(leaves.iter().map(&shl));
    let sh: Vec<Term> = leaves.iter().map(&shl).collect();
    base.extend(sh.iter().map(&shl));
    let mut level1 = vec![];
    for o in 0..5 {
        for x in &base {
            for y in &base {
                level1.push(b(o, x, y));
            }
        }
    }
    let mut pool = base.clone();
    pool.extend(level1.iter().cloned());
    pool.extend(level1.iter().map(&shl));
    pool_conjectures(pool, n, nv, 0)
}

/// Pairs over a pool with `shl1` that agree on all width-4 inputs; each is built and kernel-checked.
#[test]
#[ignore]
pub fn shl_conjecture_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    let _banner = MachineBanner::start("SHLMINER");
    let n = 4usize;
    let (nv, cap) = (env_or("SHLMINER_VARS", 2), env_or("SHLMINER_MAX", 0));
    let mut conj = shl_conjectures(nv);
    if cap > 0 && conj.len() > cap {
        let stride = conj.len() / cap;
        conj = conj.into_iter().step_by(stride).take(cap).collect();
    }
    let (mut total, mut proved, mut generic_none, mut t_none, mut carry_free, mut skipped, t0) = (0, 0, 0, 0, 0, 0, Instant::now());
    for (g0, t2) in &conj {
        let g = [g0.clone()];
        {
            let big = [&g[0], t2].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap()));
            if big {
                skipped += 1; // beyond the carry cap of add_tree_law
                continue;
            }
            total += 1;
            match prove_checked(n, nv, &format!("{} = {}", g[0].show(), t2.show()), &g[0], t2).verdict {
                Verdict::Proved => proved += 1,
                Verdict::CarryFree => carry_free += 1, // `bitwise_law` territory
                Verdict::OverCap => unreachable!("bigger laws are skipped above"),
                Verdict::NoProof { generic } => {
                    // a law that fails at another width cannot have a proof for all widths
                    t_none += 1;
                    if generic {
                        generic_none += 1;
                        if generic_none <= 12 {
                            println!("SHLMINER no proof, holds at widths 1..6: {} = {}", g[0].show(), t2.show());
                        }
                    }
                }
            }
        }
    }
    println!("SHLMINER {} listed conjectures ({} after the cap), {total} conjectures within the carry cap ({skipped} bigger ones skipped): {proved} proved and checked, {carry_free} carry-free (bitwise laws), {t_none} without a proof ({generic_none} hold at widths 1..6), {:?}", conj.len(), conj.len(), t0.elapsed());
}

/// `c * t` (mod 2^n) as shift-and-add: the sum of `shl1^i t` over the set bits `i` of `c`.
pub fn mul_const(c: u32, t: &Term) -> Term {
    let shl = |a: Term, k: u32| (0..k).fold(a, |acc, _| Term::Op(SHL1, Box::new(acc), Box::new(Term::Zero)));
    let mut parts = (0..32).filter(|i| c >> i & 1 == 1).map(|i| shl(t.clone(), i));
    let first = parts.next().expect("c is nonzero");
    parts.fold(first, |acc, p| Term::Op(ADD, Box::new(acc), Box::new(p)))
}

#[test]
pub fn multiplication_by_constants_as_shift_and_add_machines() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let shl = |a: Term| op(6, a, Term::Zero);
    let n = 4usize;
    let laws = [
        ("3x = x + 2x, written both ways", mul_const(3, &v(0)), op(0, shl(v(0)), v(0))),
        ("2x = x + x", mul_const(2, &v(0)), op(0, v(0), v(0))),
        ("6x = 2 * 3x", mul_const(6, &v(0)), shl(mul_const(3, &v(0)))),
        ("5x = 4x + x", mul_const(5, &v(0)), op(0, v(0), shl(shl(v(0))))),
        ("7x = 8x - x", mul_const(7, &v(0)), op(4, shl(shl(shl(v(0)))), v(0))),
        ("3 (x + y) = 3x + 3y", mul_const(3, &op(0, v(0), v(1))), op(0, mul_const(3, &v(0)), mul_const(3, &v(1)))),
        ("3 (x - y) = 3x - 3y", mul_const(3, &op(4, v(0), v(1))), op(4, mul_const(3, &v(0)), mul_const(3, &v(1)))),
        ("(x + y) + 2 (x + y) = 3x + 3y", op(0, op(0, v(0), v(1)), shl(op(0, v(0), v(1)))), op(0, mul_const(3, &v(0)), mul_const(3, &v(1)))),
    ];
    for (name, t1, t2) in &laws {
        assert!(t1.is_law(t2, 2), "{name} is not a law");
        let t0 = Instant::now();
        let (p, s) = add_tree_law(n, 2, t1, t2).unwrap_or_else(|| panic!("no proof: {name}"));
        let built = t0.elapsed();
        ck(name, &p, &s);
        println!("MUL {name}: build {built:?}, total {:?}", t0.elapsed());
    }
    // false: 3x is not 4x - 2
    assert!(add_tree_law(n, 2, &mul_const(3, &v(0)), &mul_const(5, &v(0))).is_none());
}

/// Constant-multiplication laws (`(a + b) x`, `(a b) x`, `a (x + y)`, `(2^j - 1) x`) for constants up to `MULMINER_MAX`
/// (default 7), each proved by `add_tree_law` and kernel-checked; prints carries per side and cost, so the carry cap
/// (env `CARRY_CAP`, default 10) can be probed.
/// The constant-multiplication laws over constants up to `max`: sums, products, differences, distribution over `x+y`, `x-y`.
pub fn mul_laws(max: u32) -> Vec<(String, Term, Term)> {
    let (x, y) = (Term::V(0), Term::V(1));
    let add = |a: Term, b: Term| Term::Op(ADD, Box::new(a), Box::new(b));
    let mut laws: Vec<(String, Term, Term)> = vec![];
    for a in 1..=max {
        for b in a..=max {
            laws.push((format!("({a}+{b})x = {a}x + {b}x"), mul_const(a + b, &x), add(mul_const(a, &x), mul_const(b, &x))));
            laws.push((format!("({a}*{b})x = {a}({b}x)"), mul_const(a * b, &x), mul_const(a, &mul_const(b, &x))));
            if b > a {
                let sub = |l: Term, r: Term| Term::Op(SUB, Box::new(l), Box::new(r));
                laws.push((format!("({b}-{a})x = {b}x - {a}x"), mul_const(b - a, &x), sub(mul_const(b, &x), mul_const(a, &x))));
            }
        }
        let sub = |l: Term, r: Term| Term::Op(SUB, Box::new(l), Box::new(r));
        laws.push((format!("{a}(x-y) = {a}x - {a}y"), mul_const(a, &sub(x.clone(), y.clone())), sub(mul_const(a, &x), mul_const(a, &y))));
        laws.push((format!("{a}(x+y) = {a}x + {a}y"), mul_const(a, &add(x.clone(), y.clone())), add(mul_const(a, &x), mul_const(a, &y))));
    }
    laws
}

#[test]
#[ignore]
pub fn mul_conjecture_miner() {
    let _scope = tatic::kernel::InternScope::enter();
    let _banner = MachineBanner::start("MULMINER");
    let max = env_or("MULMINER_MAX", 7);
    let n = 4usize;
    let only = std::env::var("MULMINER_ONLY").unwrap_or_default();
    let mut laws = mul_laws(max);
    laws.retain(|l| l.0.contains(&only));
    let (mut proved, mut none, mut capped, t0) = (0, 0, 0, Instant::now());
    for (name, t1, t2) in &laws {
        let cs = [t1, t2].map(|t| Machine::parse(t).map_or(0, |m| m.carries()));
        if !t1.is_law(t2, 2) {
            continue;
        }
        let tried = prove_checked(n, 2, name, t1, t2);
        match tried.verdict {
            Verdict::Proved => {
                proved += 1;
                println!("MULMINER {name}: carries {cs:?}, build {:?}, total {:?}", tried.law, tried.law + tried.check);
            }
            Verdict::OverCap => {
                capped += 1;
                println!("MULMINER {name}: carries {cs:?} over the cap");
            }
            _ => {
                none += 1;
                println!("MULMINER {name}: carries {cs:?}, NO PROOF though it holds at widths 1..6");
            }
        }
    }
    println!("MULMINER {} laws, {proved} proved and checked, {capped} over the carry cap, {none} unproved within it, {:?}", laws.len(), t0.elapsed());
}

/// Ablation audit (search note section 32): for each mul law, what a lemma-finding search would have to invent. The
/// proof's lemmas `Id(F_j, G_j(bits, phi(carries)))` are decided by the diagram prover once the midpoint (the phi
/// encodings and the tables `g`) is given, and the midpoint is the coarsest bisimulation, found by `moore_encoding`.
/// Prints per law: carries per side, states, classes, phi bits, table bits of `g`, the Moore time, the total time.
#[test]
#[ignore]
pub fn ablation_audit() {
    let _scope = tatic::kernel::InternScope::enter();
    let _banner = MachineBanner::start("AUDIT");
    let max = env_or("MULMINER_MAX", 7);
    let gops = GoodOps::new();
    let (mut n_laws, mut moore_ns, mut total_ns) = (0, 0u128, 0u128);
    for (name, t1, t2) in mul_laws(max) {
        let (Some(m1), Some(m2)) = (Machine::parse(&t1), Machine::parse(&t2)) else { continue };
        if !t1.is_law(&t2, 2) || m1.carries().max(m2.carries()) > carry_cap() {
            continue;
        }
        let t = Instant::now();
        let Some(enc) = moore_encoding(&m1, &m2, 2, &gops, None) else { continue };
        let moore = t.elapsed();
        let t = Instant::now();
        let proved = add_tree_law(4, 2, &t1, &t2).is_some();
        let total = t.elapsed();
        let m = enc.phi[0].len();
        let classes = (0..2).map(|s| enc.phi[s][0].len()).collect::<Vec<_>>();
        let gbits = (1 + m) << (2 + m);
        n_laws += 1;
        moore_ns += moore.as_nanos();
        total_ns += total.as_nanos();
        println!("AUDIT {name}: carries [{}, {}], states {classes:?}, phi bits {m}, g bits {gbits}, moore {moore:?}, proof {total:?}, proved {proved}", m1.carries(), m2.carries());
    }
    println!("AUDIT {n_laws} laws, Moore {:.1}s of {:.1}s proof time", moore_ns as f64 / 1e9, total_ns as f64 / 1e9);
}

// ---- Proof-producing decision diagrams (search note section 29). Each lemma over `nv` bits used to be a full case
// tree (2^nv leaves). Here every signal carries a reduced ordered decision diagram node `n` and a kernel proof
// `Id(e, C(n))` that its gate expression equals the node's canonical term `C(n)` (nested `mux` over the bit variables),
// built gate by gate: `op(C(a), C(b)) = C(apply(op, a, b))` is proved by recursion on the diagrams (Harrison's BDD rule
// for HOL, 1995), each step an instance of a closed lemma, memoized per node pair. Two signals have the same node iff
// they are the same Boolean function, so an equality lemma is `trans` of one proof with the `sym` of the other.
