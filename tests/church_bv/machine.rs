use super::rewrite::Node;
use super::*;

/// The value of an add-free bitwise term at one bit position, with its `GoodBool` witness, given the operand bits.
pub fn term_gb<G: Gates>(g: &G, tm: &Term, u: &[G::S]) -> G::S {
    match *tm.node() {
        Node::V(i) => u[i].clone(),
        Node::Zero => g.konst(false),
        Node::Ones => g.konst(true),
        Node::Op(AND, a, b) => g.and(&term_gb(g, &a, u), &term_gb(g, &b, u)),
        Node::Op(OR, a, b) => g.or(&term_gb(g, &a, u), &term_gb(g, &b, u)),
        Node::Op(XOR, a, b) => g.xor(&term_gb(g, &a, u), &term_gb(g, &b, u)),
        Node::Op(..) => panic!("`add` inside a leaf"),
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
    /// `(left, right, op)`, `op` as in `Node::Op`: add (0) and sub (4) nodes carry a bit between positions, the
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
        fn go(t: &Term, m: &mut Machine, seen: &mut hashbrown::HashMap<Term, Src>) -> Option<Src> {
            match *t.node() {
                Node::Op(o, a, b) => {
                    if o == SHR1 {
                        return None; // a right shift reads a later position: not a left-to-right machine
                    }
                    let key = *t;
                    if let Some(src) = seen.get(&key) {
                        return Some(*src);
                    }
                    let a = go(&a, m, seen)?;
                    let b = if o == SHL1 { a } else { go(&b, m, seen)? };
                    m.nodes.push((a, b, o));
                    let src = Src::Node(m.nodes.len() - 1);
                    seen.insert(key, src);
                    Some(src)
                }
                _ => {
                    m.leaves.push(*t);
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

/// Each machine's (out, next carries) on all assignments of (operand bits, carries), in plain Booleans.
pub fn raw_table(mach: &Machine, k: usize) -> Vec<Vec<bool>> {
    let c = mach.carries();
    (0..1usize << (k + c))
        .map(|r| {
            let bits: Vec<bool> = (0..k + c).map(|pos| r >> (k + c - 1 - pos) & 1 == 1).collect();
            let (o, next) = mach.step(&Bools, &bits[..k], &bits[k..]);
            std::iter::once(!mach.last() && o).chain(next).collect()
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
pub fn moore_encoding(m1: &Machine, m2: &Machine, k: usize, reach: Option<&Reach>) -> Option<Encoding> {
    let raw = [raw_table(m1, k), raw_table(m2, k)];
    let cs = [m1.carries(), m2.carries()];
    let last = m1.last();
    let live = |side: usize, s: usize| reach.is_none_or(|rc| rc[side][s]);
    // class[side][s]; unreachable vectors stay in class 0 and are never looked at
    let mut class: [Vec<usize>; 2] = [0, 1].map(|side| (0..1usize << cs[side]).map(|s| if last && live(side, s) { s & 1 } else { 0 }).collect());
    let mut count = 0;
    loop {
        let mut ids: hashbrown::HashMap<Vec<(usize, bool, usize)>, usize> = Default::default();
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
    let fmap = lam(bl, mux(var(0), shift(a, 0, 1), shift(b, 0, 1)));
    let p = cong1(&bl, &bl, &fmap, f(), t(), h);
    sym(&bl, &app(fmap, f()), &app(fmap, t()), p)
}


/// The machine-state reader shared with `tools/runs` (std only, so the file compiles here as it is).
#[cfg(windows)]
#[path = "../../tools/runs/src/state.rs"]
pub mod state;

/// Defender's real-time protection and the machine's CPU load over 2 s (`RTP=False CPU=18%`), read natively
/// (`tools/runs/src/state.rs`); "machine state unavailable" off Windows.
pub fn rtp_cpu() -> String {
    #[cfg(windows)]
    return state::rtp_cpu();
    #[cfg(not(windows))]
    return "machine state unavailable".to_string();
}

/// `lockpriv=True pages=large`: whether this process holds the "Lock pages in memory" privilege, and whether it
/// allocates from large OS pages. mimalloc enables the privilege itself when the option is on, so both together mean
/// large pages.
pub fn pages_text() -> String {
    #[cfg(windows)]
    let lock = state::lockpriv();
    #[cfg(not(windows))]
    let lock = false;
    let pages = if large_pages_option() && lock { "large" } else { "normal" };
    format!("lockpriv={} pages={pages}", if lock { "True" } else { "False" })
}

/// One line of machine state to print with every timing (LONG_RUNS.md): `RTP=.. CPU=..% lockpriv=.. pages=..`, in
/// about 2 s (the CPU sample).
pub fn machine_state() -> String {
    format!("{} {}", rtp_cpu(), pages_text())
}

/// mimalloc's `allow_large_os_pages` option in this process: the build's default (`.cargo/config.toml`) unless
/// `MIMALLOC_ALLOW_LARGE_OS_PAGES` overrides it.
pub fn large_pages_option() -> bool {
    unsafe extern "C" {
        fn mi_option_get(option: std::ffi::c_int) -> std::ffi::c_long;
    }
    // `mi_option_allow_large_os_pages` in mimalloc v3's option list
    unsafe { mi_option_get(6) != 0 }
}

/// The build turns large pages on: fails if `.cargo/config.toml`'s define stops reaching mimalloc.
#[test]
#[cfg(all(windows, target_env = "msvc"))]
pub fn mimalloc_defaults_to_large_pages() {
    let job = &Job::new(Setup::process());
    if job.setup().var("MIMALLOC_ALLOW_LARGE_OS_PAGES").is_none() {
        assert!(large_pages_option());
    }
}

/// `pages_text` is what the driver appends to its machine-state line.
#[test]
fn pages_text_has_both_fields() {
    let t = pages_text();
    assert!(t.starts_with("lockpriv=True pages=") || t.starts_with("lockpriv=False pages="), "{t}");
    assert!(t.ends_with("pages=large") || t.ends_with("pages=normal"), "{t}");
}

/// Prints the machine state (Defender, CPU load) when created and again when dropped, so a timing run records both ends.
/// `MACHINE_BANNER=0` silences it (each state costs about 2 s): `driver::loop_stream` records the state once per loop instead.
pub struct MachineBanner(&'static str);
impl MachineBanner {
    pub fn start(job: &Job, tag: &'static str) -> Self {
        if !job.setup().flag("MACHINE_BANNER", true) {
            return MachineBanner("");
        }
        println!("{tag} machine at start: {}", machine_state());
        MachineBanner(tag)
    }
}
impl Drop for MachineBanner {
    fn drop(&mut self) {
        if !self.0.is_empty() {
            println!("{} machine at end: {}", self.0, machine_state());
        }
    }
}

/// Prints one machine-state line, for a human: `cargo test --release --test church_bv machine::machine_state_line --
/// --exact --ignored --nocapture`. The driver composes its own (`driver::machine_state`).
#[test]
#[ignore]
pub fn machine_state_line() {
    println!("machine state: {}", machine_state());
}

/// The driver's worker task for the part of the state that belongs to the children's process and environment.
#[test]
#[ignore]
pub fn pages_line() {
    pages_line_task(&Setup::process())
}

pub fn pages_line_task(setup: &Arc<Setup>) {
    let pages = pages_text();
    println!("pages: {pages}");
    setup.result("pages", pages);
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
pub fn prove_checked(job: &Job, n: usize, nv: usize, name: &str, t1: &Term, t2: &Term) -> Tried {
    let t = Instant::now();
    let law = add_tree_law(job, n, nv, t1, t2);
    let law_time = t.elapsed();
    let verdict = match law {
        Some((p, s)) => {
            let t = Instant::now();
            ck(name, &p, &s);
            return Tried { verdict: Verdict::Proved, law: law_time, check: t.elapsed() };
        }
        None => {
            let carries = [t1, t2].map(|t| Machine::parse(t).map_or(0, |m| m.carries())).into_iter().max().unwrap_or(0);
            if carries > carry_cap(job) {
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

/// The most carries per side `add_tree_law` takes on (its lemmas are case trees over `k + carries` bits); env `CARRY_CAP`.
pub fn carry_cap(job: &Job) -> usize {
    job.setup().or("CARRY_CAP", 10)
}

thread_local! {
    /// `add_tree_law` results (a closed proof, or none) by width, variable count and the two terms: the rewriter asks for the same
    /// pair again for every law and every mined candidate that reaches the same subterm.
    static TREE_LAWS: std::cell::RefCell<hashbrown::HashMap<(usize, usize, Term, Term), Option<(tatic::kernel::PExpr, tatic::kernel::PExpr)>>> = Default::default();
}

/// `tree_encoding` results past its cheap screens, by the same key, shared by a process's threads behind one lock: per thread,
/// 87.6% of a sweep's searches redid another thread's (docs/tier-cycle.md, "Survey: long-lived sweep workers"). Pure in its key;
/// `carry_cap()` is a screen before the lookup.
static TREE_ENCS: crate::task::SharedMemo<(usize, usize, Term, Term), Option<std::sync::Arc<TreeEnc>>> = crate::task::SharedMemo::new();

/// What `tree_encoding` found for a pair: the carry encoding, and the reachable carry states it holds over (`None`: all of them).
pub struct TreeEnc {
    enc: Encoding,
    inv: Option<Reach>,
}

/// Whether `t1 = t2` (two sum trees of add-free leaves over `k` good vectors) has a carry encoding, and which: found by
/// `moore_encoding`, first over all carry states, then over the reachable ones; `None` when there is none. Builds no kernel terms.
pub fn tree_encoding(job: &Job, n: usize, k: usize, t1: &Term, t2: &Term) -> Option<std::sync::Arc<TreeEnc>> {
    // the cheap screens are not cached (`tree_step` offers only candidates that pass the first)
    if !t1.plausibly_equals(t2, n, k) {
        return None;
    }
    let (m1, m2) = (Machine::parse(t1)?, Machine::parse(t2)?);
    if m1.last() != m2.last() {
        return None;
    }
    let cs = [m1.carries(), m2.carries()];
    if cs[0].max(cs[1]) > carry_cap(job) || cs[0] + cs[1] == 0 {
        return None;
    }
    let key = (n, k, *t1, *t2);
    if let Some(hit) = TREE_ENCS.get(&key) {
        return hit;
    }
    // the search runs unlocked: two threads may both search a pair, and find the same encoding
    let attempt = |reach: Option<&Reach>| moore_encoding(&m1, &m2, k, reach);
    // first over all carry states; failing that, over the reachable ones, with the lemmas conditional on an invariant
    let found = match attempt(None) {
        Some(enc) => Some(TreeEnc { enc, inv: None }),
        // guarded lemmas are still case trees over k + c bits, so they keep the old cap
        None if cs[0].max(cs[1]) > 6 => None,
        None => {
            let r = [reachable(&raw_table(&m1, k)), reachable(&raw_table(&m2, k))];
            let second = if r.iter().all(|v| v.iter().all(|x| *x)) { None } else { attempt(Some(&r)) };
            second.map(|enc| TreeEnc { enc, inv: Some(r) })
        }
    }
    .map(std::sync::Arc::new);
    TREE_ENCS.insert(key, found.clone());
    found
}

/// Proof of `t1 = t2` for two sum trees of add-free leaves over `k` good vectors, from their carry encoding (`tree_encoding`);
/// `None` when there is none.
pub fn add_tree_law(job: &Job, n: usize, k: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    let key = (n, k, *t1, *t2);
    if let Some(hit) = TREE_LAWS.with(|c| c.borrow().get(&key).map(|l| l.as_ref().map(|(p, s)| (p.get(), s.get())))) {
        return hit;
    }
    let law = tree_encoding(job, n, k, t1, t2).map(|found| tree_proof(job, n, k, t1, t2, &found));
    TREE_LAWS.with(|c| c.borrow_mut().insert(key, law.map(|(p, s)| (tatic::kernel::persist(p), tatic::kernel::persist(s)))));
    law
}

fn tree_proof(job: &Job, n: usize, k: usize, t1: &Term, t2: &Term, found: &TreeEnc) -> (Expr, Expr) {
    let (m1, m2) = (Machine::parse(t1).expect("a machine"), Machine::parse(t2).expect("a machine"));
    let last = m1.last();
    let cs = [m1.carries(), m2.carries()];
    let (enc, inv) = (&found.enc, &found.inv);
    let gops = GoodOps::new();
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
    // a side's step at (operand bits, carries): (output, next carries)
    let step_of = |side: usize, v: &[Expr]| -> (Expr, Vec<Expr>) {
        let dummy: Vec<Gb> = v.iter().map(|e| Gb { e: *e, g: f() }).collect();
        let (o, next) = machines[side].step(&gops, &dummy[..k], &dummy[k..]);
        (o.e, next.into_iter().map(|g| g.e).collect())
    };
    // F_j of a side at symbolic (operand bits, carries): j = 0 output, 1..=m the next phi values
    let side_f = |side: usize, j: usize, v: &[Expr]| -> Expr {
        let (o, next) = step_of(side, v);
        match j {
            0 => o,
            _ => phi_expr(side, j - 1, &next),
        }
    };
    // at a leaf's literal bits, once for the side's m + 1 F lemmas and its P lemma: (output, next carries, phi of the carries)
    type Step = std::rc::Rc<(Expr, Vec<Expr>, Vec<Expr>)>;
    let steps: std::cell::RefCell<hashbrown::HashMap<(usize, Vec<bool>), Step>> = Default::default();
    let step_at = |side: usize, v: &[Expr], bits: Option<&[bool]>| -> Step {
        let build = || {
            let (o, next) = step_of(side, v);
            std::rc::Rc::new((o, next, (0..m).map(|q| phi_expr(side, q, &v[k..])).collect()))
        };
        let Some(bits) = bits else { return build() };
        if let Some(hit) = steps.borrow().get(&(side, bits.to_vec())) {
            return hit.clone();
        }
        let s = build();
        steps.borrow_mut().insert((side, bits.to_vec()), s.clone());
        s
    };
    let inv_expr = |side: usize, v: &[Expr]| table_app(v, &|b| inv.as_ref().unwrap()[side][index_of(b)]);
    // `Id(a, b)` for the `nv` bits `v` by case analysis; the carries are `v[off..]`. Over the reachable states only
    // (with `inv`), the lemma takes `Id(I(carries), true)` and the unreachable cases are absurd.
    // decision-diagram proofs lost to the case tree at nv = 9 and 11 (docs/tier-cycle.md, "Decision diagrams deleted")
    // `ab` gets the bits too at a leaf (`Some`), the symbolic ones in the statement (`None`)
    type CaseFn<'a> = dyn Fn(&[Expr], Option<&[bool]>) -> (Expr, Expr) + 'a;
    let guarded = |side: usize, nv: usize, off: usize, tag: &str, ab: &CaseFn<'_>| -> Expr {
        // shared across conjectures: keyed on the side machine, the encoding tables and the lemma tag
        let key = format!("tree|{}|{k}|{nv}|{tag}|{:?}|{:?}", machines[side].key(), inv.as_ref().map(|r| &r[side]), enc.phi[side]);
        shared_lemma(job.setup(), key, || {
            let hty = |v: &[Expr]| id(bool0(), inv_expr(side, &v[off..]), t());
            let body = |v: &[Expr]| {
                let (a, b) = ab(v, None);
                let inner = id(bool0(), a, b);
                if inv.is_some() { pi(hty(v), shift(&inner, 0, 1)) } else { inner }
            };
            let ty = lemma_n_ty(nv, &body);
            if inv.is_some() && job.setup().flag("GUARDTRACE", false) {
                eprintln!("GUARDED lemma nv={nv} tag={tag}");
            }
            let leaf = |bits: &[bool]| {
                let lits: Vec<Expr> = bits.iter().map(|b| bit(*b)).collect();
                let (a, b) = ab(&lits, Some(bits));
                match &inv {
                    None => refl(a),
                    Some(r) => lam(hty(&lits), if r[side][index_of(&bits[off..])] { refl(a) } else { absurd_id(var(0), &a, &b) }),
                }
            };
            (lemma_n(nv, &body, &leaf).0, ty)
        })
        .0
    };
    // lemmas Id(F_j, G_j(operand bits, phi(carries))) by case analysis on the k + c bits
    let lemmas: Vec<Vec<Expr>> = (0..2)
        .map(|side| {
            (0..=m)
                .map(|j| {
                    if last && j == 0 {
                        return t();
                    }
                    guarded(side, k + cs[side], k, &format!("F{j}|{:?}", enc.g[j]), &|v, bits| {
                        let s = step_at(side, v, bits);
                        let key: Vec<Expr> = v[..k].iter().chain(&s.2).cloned().collect();
                        (if j == 0 { s.0 } else { phi_expr(side, j - 1, &s.1) }, g_expr(j, &key))
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
            guarded(side, k + cs[side], k, "P", &|v, bits| (inv_expr(side, &step_at(side, v, bits).1), t()))
        })
        .collect();
    let dec_expr = |v: &[Expr]| table_app(v, &|b| dec[index_of(b)]);
    // the last carry is a function of the phi values: Id(carry_last, dec(phi(carries))) by cases
    let dlemmas: Vec<Expr> = (0..2)
        .map(|side| {
            if !last {
                return t();
            }
            guarded(side, cs[side], 0, &format!("D|{dec:?}"), &|v, _| (v[cs[side] - 1], dec_expr(&(0..m).map(|q| phi_expr(side, q, v)).collect::<Vec<_>>())))
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
            let ub: Vec<Expr> = ug.iter().map(|g| g.e).collect();
            let sx = |side: usize| -> Vec<Expr> { st[side].iter().map(|g| g.e).collect() };
            let vs = |side: usize| -> Vec<Expr> { ub.iter().cloned().chain(sx(side)).collect() };
            let pq = |side: usize| -> Vec<Expr> { (0..m).map(|j| phi_expr(side, j, &sx(side))).collect() };
            let key = |p: &[Expr]| -> Vec<Expr> { ub.iter().cloned().chain(p.iter().cloned()).collect() };
            let eq = |j: usize| {
                let (fl, fr) = (side_f(0, j, &vs(0)), side_f(1, j, &vs(1)));
                let (pl, pr) = (pq(0), pq(1));
                let (gl, gr) = (g_expr(j, &key(&pl)), g_expr(j, &key(&pr)));
                let inst = |side: usize| {
                    let args = vs(side).into_iter().chain(ug.iter().map(|g| g.g)).chain(st[side].iter().map(|g| g.g));
                    let mut args: Vec<Expr> = args.collect();
                    if inv.is_some() {
                        args.push(hy[side]);
                    }
                    apps(lemmas[side][j], args)
                };
                let mut fmap = g_expr(j, &ub.iter().map(|e| shift(e, 0, m as i32)).chain((0..m).map(|q| var((m - 1 - q) as u32))).collect::<Vec<_>>());
                for _ in 0..m {
                    fmap = lam(bl, fmap);
                }
                let link = cong_n(&bl, &bl, &fmap, &pl, &pr, ip.clone());
                let back = sym(&bl, &fr, &gr, inst(1));
                let mid = tr(&gl, &gr, &fr, link, back);
                (fl, fr, tr(&fl, &gl, &fr, inst(0), mid))
            };
            let first = last as usize;
            let proofs: Vec<(Expr, Expr, Expr)> = (first..=m).map(eq).collect();
            if !last {
                s1.push(proofs[0].0);
                s2.push(proofs[0].1);
                e.push(proofs[0].2);
            }
            ip = proofs[1 - first..].iter().map(|p| p.2).collect();
            if inv.is_some() {
                for side in 0..2 {
                    let args = vs(side).into_iter().chain(ug.iter().map(|g| g.g)).chain(st[side].iter().map(|g| g.g)).chain([hy[side]]);
                    hy[side] = apps(pres[side], args.collect());
                }
            }
            for side in 0..2 {
                st[side] = machines[side].step(&gops, &ug, &st[side]).1;
            }
        }
        (s1, s2, e, st, ip, hy)
    };
    if !last {
        return k_var_law(n, k, t1, t2, &|bits, goods| {
            let (s1, s2, e, ..) = core(bits, goods);
            (s1, s2, e)
        });
    }
    k_var_law_to(n, k, &bv_ty(1), &|args| (t1.eval(&ops_for(n), n, args), t2.eval(&ops_for(n), n, args)), &|bits, goods| {
        let (.., st, ip, hy) = core(bits, goods);
        let bl = bool0();
        let sx = |side: usize| -> Vec<Expr> { st[side].iter().map(|g| g.e).collect() };
        let pq = |side: usize| -> Vec<Expr> { (0..m).map(|j| phi_expr(side, j, &sx(side))).collect() };
        let (pl, pr) = (pq(0), pq(1));
        let end = |side: usize| st[side][cs[side] - 1].e;
        let inst = |side: usize| {
            let mut args: Vec<Expr> = sx(side).into_iter().chain(st[side].iter().map(|g| g.g)).collect();
            if inv.is_some() {
                args.push(hy[side]);
            }
            apps(dlemmas[side], args)
        };
        let (dl, dr) = (dec_expr(&pl), dec_expr(&pr));
        let mut fmap = dec_expr(&(0..m).map(|q| var((m - 1 - q) as u32)).collect::<Vec<_>>());
        for _ in 0..m {
            fmap = lam(bl, fmap);
        }
        let link = cong_n(&bl, &bl, &fmap, &pl, &pr, ip);
        let back = sym(&bl, &end(1), &dr, inst(1));
        let mid = trans_proof(&bl, &dl, &dr, &end(1), link, back);
        let whole = trans_proof(&bl, &end(0), &dl, &end(1), inst(0), mid);
        let fbody = lam(bl, lam(sort(1), lam(karrow(1), app(var(0), var(2)))));
        cong_n(&bl, &bv_ty(1), &fbody, &[end(0)], &[end(1)], vec![whole])
    })
}

#[test]
pub fn state_encoding_search_proves_three_leaf_sum_laws() {
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |a: Term, b: Term| Term::op(ADD, a, b);
        for n in [1usize, 2, 4] {
            for (name, t1, t2) in [
                ("add (add x y) y = add x (add y y)", op(op(v(0), v(1)), v(1)), op(v(0), op(v(1), v(1)))),
                ("add (add y y) -1 = add y (add y -1)", op(op(v(1), v(1)), Term::ONES), op(v(1), op(v(1), Term::ONES))),
                ("add (add x -1) -1 = add x (add -1 -1)", op(op(v(0), Term::ONES), Term::ONES), op(v(0), op(Term::ONES, Term::ONES))),
            ] {
                if n == 1 {
                    let e = moore_encoding(&Machine::parse(&t1).unwrap(), &Machine::parse(&t2).unwrap(), 2, None).unwrap();
                    println!("ENCODING {name}: {} phi bits, phi1 {:?}", e.phi[0].len(), e.phi[0]);
                }
                let (p, s) = add_tree_law(job, n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no encoding"));
                ck(&format!("{name} at n={n}"), &p, &s);
            }
            // a false law has no encoding
            assert!(add_tree_law(job, n, 2, &op(op(v(0), v(1)), v(1)), &op(v(0), op(v(0), v(0)))).is_none());
        }
    })
}

#[test]
pub fn state_encoding_search_handles_bitwise_leaves_three_vectors_and_four_leaves() {
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let add = |a: Term, b: Term| op(0, a, b);
        for n in [1usize, 2, 4] {
            // x & y + x | y = x + y: the leaves are bitwise terms
            let t1 = add(op(1, v(0), v(1)), op(2, v(0), v(1)));
            let t2 = add(v(0), v(1));
            let (p, s) = add_tree_law(job, n, 2, &t1, &t2).expect("and+or");
            ck(&format!("and+or at n={n}"), &p, &s);
            // associativity over three vectors, found by search
            let (p, s) = add_tree_law(job, n, 3, &add(add(v(0), v(1)), v(2)), &add(v(0), add(v(1), v(2)))).expect("assoc3");
            ck(&format!("assoc over x y z at n={n}"), &p, &s);
            // four leaves (three carries, two-bit total carry): (((x+y)+z)+x) = (x+(y+(z+x)))
            let l = add(add(add(v(0), v(1)), v(2)), v(0));
            let r = add(v(0), add(v(1), add(v(2), v(0))));
            let (p, s) = add_tree_law(job, n, 3, &l, &r).expect("four leaves");
            ck(&format!("four leaves at n={n}"), &p, &s);
            // false laws have no encoding
            assert!(add_tree_law(job, n, 3, &l, &add(v(0), add(v(1), add(v(2), v(2))))).is_none());
            assert!(add_tree_law(job, n, 2, &t1, &add(v(0), v(0))).is_none());
        }
    })
}

#[test]
pub fn symmetric_encoding_handles_unequal_carry_counts_bare_leaves_and_five_leaves() {
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let add = |a: Term, b: Term| op(0, a, b);
        for n in [1usize, 2, 4] {
            // one add against two: the zero leaf adds a carry that never fires
            let (p, s) = add_tree_law(job, n, 2, &add(v(1), Term::ONES), &add(Term::ONES, add(v(1), Term::ZERO))).expect("unequal counts");
            ck(&format!("y + -1 = -1 + (y + 0) at n={n}"), &p, &s);
            // a bare leaf is a sum with no carries
            let (p, s) = add_tree_law(job, n, 2, &v(1), &add(v(1), Term::ZERO)).expect("bare leaf");
            ck(&format!("y = y + 0 at n={n}"), &p, &s);
            let (p, s) = add_tree_law(job, n, 2, &op(3, v(0), Term::ONES), &add(op(3, v(0), Term::ONES), Term::ZERO)).expect("bare bitwise leaf");
            ck(&format!("x^-1 = (x^-1) + 0 at n={n}"), &p, &s);
            assert!(add_tree_law(job, n, 2, &v(1), &add(v(1), Term::ONES)).is_none());
            // five leaves, four carries
            let l = add(add(add(add(v(0), v(1)), v(2)), v(0)), v(1));
            let r = add(v(0), add(v(1), add(v(2), add(v(0), v(1)))));
            let (p, s) = add_tree_law(job, n, 3, &l, &r).expect("five leaves");
            ck(&format!("five leaves at n={n}"), &p, &s);
            assert!(add_tree_law(job, n, 3, &l, &add(v(0), add(v(1), add(v(2), add(v(0), v(0)))))).is_none());
            assert!(add_tree_law(job, n, 2, &add(v(1), Term::ONES), &add(v(0), add(v(1), Term::ZERO))).is_none());
        }
    })
}

/// Build and check time of the carry-encoding proof by number of carries (n = 4, three operands).
#[test]
#[ignore]
pub fn tree_proof_cost_by_carries() {
    let job = &Job::new(Setup::process());
    let v = |i: usize| Term::v(i);
    let add = |a: Term, b: Term| Term::op(ADD, a, b);
    let leaves = [v(0), v(1), v(2), v(0), v(1), v(2), v(0)];
    for n in [4usize] {
        for c in 2..=6usize {
            let left = leaves[1..=c].iter().fold(leaves[0], |a, b| add(a, *b));
            let right = leaves[..c].iter().rev().fold(leaves[c], |a, b| add(*b, a));
            tatic::kernel::scoped(|| {
                let t0 = Instant::now();
                let (p, s) = add_tree_law(job, n, 3, &left, &right).expect("encoding");
                let built = t0.elapsed();
                let t1 = Instant::now();
                let ok = holds(&p, &s).is_ok();
                println!("TREECOST n={n} carries={c}: build {built:?}, check {:?}, ok {ok}", t1.elapsed());
            })
        }
    }
}

#[test]
pub fn sub_computes_is_good_and_its_laws_are_found_by_the_encoding_search() {
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
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
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        for n in [1usize, 2, 4] {
            for (name, k, l, r) in [
                ("x - x = 0", 2, op(4, v(0), v(0)), Term::ZERO),
                ("x - 0 = x", 2, op(4, v(0), Term::ZERO), v(0)),
                ("(x + y) - y = x", 2, op(4, op(0, v(0), v(1)), v(1)), v(0)),
                ("(x - y) + y = x", 2, op(0, op(4, v(0), v(1)), v(1)), v(0)),
                ("(x - y) - z = x - (y + z)", 3, op(4, op(4, v(0), v(1)), v(2)), op(4, v(0), op(0, v(1), v(2)))),
                ("0 - x = ~(x + -1)", 2, op(4, Term::ZERO, v(0)), op(3, op(0, v(0), Term::ONES), Term::ONES)),
                ("~(x + y) = ~x - y", 2, op(3, op(0, v(0), v(1)), Term::ONES), op(4, op(3, v(0), Term::ONES), v(1))),
                ("(x & y) + (x | y) = x + y, bitwise nodes inside the machine", 2, op(0, op(1, v(0), v(1)), op(2, v(0), v(1))), op(0, v(0), v(1))),
                ("x - (y - z) = (x - y) + z", 3, op(4, v(0), op(4, v(1), v(2))), op(0, op(4, v(0), v(1)), v(2))),
            ] {
                let (p, s) = add_tree_law(job, n, k, &l, &r).unwrap_or_else(|| panic!("{name}: no encoding"));
                ck(&format!("{name} at n={n}"), &p, &s);
            }
            // false laws have none
            assert!(add_tree_law(job, n, 2, &op(4, v(0), v(1)), &op(4, v(1), v(0))).is_none());
            assert!(add_tree_law(job, n, 2, &op(4, v(0), v(1)), &op(0, v(0), v(1))).is_none() || n == 1);
        }
    })
}

/// The decisions are made in plain Booleans (`Bools`); the kernel's gates (`GoodOps`, normalized) must give the same machine
/// steps, so the plain decisions match what the proofs then state.
#[test]
pub fn plain_steps_match_the_kernel_gates() {
    tatic::kernel::scoped(|| {
        let (v, op) = (|i: usize| Term::v(i), |o: usize, a: Term, b: Term| Term::op(o, a, b));
        let gops = GoodOps::new();
        for term in [op(ADD, op(XOR, v(0), Term::ONES), v(1)), op(SUB, v(0), op(AND, v(0), v(1))), op(5, op(ADD, v(0), v(1)), op(OR, v(1), v(0))), op(ADD, op(ADD, v(0), v(1)), op(SUB, v(1), v(0)))] {
            let m = Machine::parse(&term).unwrap();
            let (k, c) = (2, m.carries());
            for r in 0..1usize << (k + c) {
                let bits: Vec<bool> = (0..k + c).map(|p| r >> p & 1 == 1).collect();
                let gbs: Vec<Gb> = bits.iter().map(|b| Gb { e: bit(*b), g: f() }).collect();
                let (o, next) = m.step(&Bools, &bits[..k], &bits[k..]);
                let (oe, nexte) = m.step(&gops, &gbs[..k], &gbs[k..]);
                let kernel: Vec<bool> = std::iter::once(&oe).chain(&nexte).map(|g| normalize(&g.e) == t()).collect();
                assert_eq!(std::iter::once(o).chain(next).collect::<Vec<_>>(), kernel, "{} at {bits:?}", term.show());
            }
        }
    })
}

/// Mine at width `MINER_N` (default 4) over `MINER_VARS` variables (default 2), `MINER_DEEP=1` for terms two
/// operators deep. Prints the classes, then tries every conjecture over x, y with the generic builder.
#[test]
#[ignore]
pub fn conjecture_miner() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let (n, nvars, deep) = (job.setup().or("MINER_N", 4), job.setup().or("MINER_VARS", 2), job.setup().flag("MINER_DEEP", false));
        let ts = terms(job.setup(), nvars, deep);
        let t0 = Instant::now();
        // classes by the values on the tuples (variable `i` is bits `n*i..` of a tuple)
        let mut classes: std::collections::BTreeMap<Vec<u128>, Vec<usize>> = Default::default();
        // all input tuples, or `MINER_SAMPLE` of them (a fixed pseudo-random subset plus the all-zero and all-one
        // tuples): a class may then hold a false equality, which no proof builder or kernel check will accept
        let total = 1u128 << (n * nvars);
        let sample = job.setup().or("MINER_SAMPLE", 0) as u128;
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
            let values = tuples.iter().map(|&tu| t.interp(n, &(0..nvars).map(|v| tu >> (n * v) & low_bits(n)).collect::<Vec<_>>())).collect();
            classes.entry(values).or_default().push(i);
        }
        let conjectures: usize = classes.values().map(|c| c.len() - 1).sum();
        println!("MINER n={n} vars={nvars} deep={deep}: {} terms, {} classes, {conjectures} conjectures, run in {:?}", ts.len(), classes.len(), t0.elapsed());
        let show = job.setup().flag("MINER_SHOW", false);
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
                    match rewrite_law(job, n, k, members[0], other) {
                        Some((p, s)) if k > 2 && holds(&p, &s).is_ok() => by_third.1 += 1,
                        _ if k > 2 => match add_tree_law(job, n, k, members[0], other) {
                            Some((p, s)) if holds(&p, &s).is_ok() => by_third.1 += 1,
                            _ => needs_z += 1,
                        },
                        Some((p, s)) if holds(&p, &s).is_ok() => by_rewrite += 1,
                        Some(_) => rewrite_bugs.push(law),
                        None => {
                            // the generic carry-chain builder, in either orientation
                            let chain = carry_chain_law(n, members[0], other).or_else(|| carry_chain_law(n, other, members[0]));
                            match chain {
                                Some((p, s)) if holds(&p, &s).is_ok() => by_chain += 1,
                                _ => match add_tree_law(job, n, 2, members[0], other) {
                                    Some((p, s)) if holds(&p, &s).is_ok() => by_tree += 1,
                                    _ => needs_add.push(law),
                                },
                            }
                        }
                    }
                } else {
                    let (p, s) = bitwise_law_k(n, k, members[0], other);
                    if holds(&p, &s).is_ok() {
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
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let same = |a: &Term, b: &Term| {
            classes.values().any(|c| c.iter().any(|&i| ts[i] == *a) && c.iter().any(|&i| ts[i] == *b))
        };
        let (p0, s0) = add_zero_proof(n, 0);
        let (p1, s1) = add_identity_proof(n, 0, true);
        let (p2, s2) = add_comm_proof(n, false);
        for (name, mined, proved) in [
            ("add x 0 = x", same(&op(0, v(0), Term::ZERO), &v(0)), holds(&p0, &s0).is_ok()),
            ("add 0 x = x", same(&op(0, Term::ZERO, v(0)), &v(0)), holds(&p1, &s1).is_ok()),
            ("add x y = add y x", same(&op(0, v(0), v(1)), &op(0, v(1), v(0))), holds(&p2, &s2).is_ok()),
        ] {
            println!("MINER known lemma {name}: conjectured {mined}, template proof checks {proved}");
            assert!(mined && proved, "{name}");
        }
        if deep && nvars >= 3 {
            let assoc = same(&op(0, op(0, v(0), v(1)), v(2)), &op(0, v(0), op(0, v(1), v(2))));
            println!("MINER add associativity conjectured: {assoc}");
        }
    })
}

// ---- Comparison (search note section 20): `lt a b` is the final borrow of the chain for `a - b`, a `Bool0` result.

/// The conjectures of a term pool: terms with equal values on every width-`n` tuple of `nv` variables are paired with
/// the group's first member, sorted for a stable order and, when `cap` is nonzero, sampled by stride down to about `cap`.
pub fn pool_conjectures(pool: impl IntoIterator<Item = Term>, n: usize, nv: usize, cap: usize) -> Vec<(Term, Term)> {
    let mut memo = ValueMemo::exhaustive(n, nv);
    let mut groups: hashbrown::HashMap<Vec<u8>, Vec<Term>> = Default::default();
    for t in pool {
        // a comparison (one-bit result) never equals an n-bit term, even when their signatures coincide
        let mut key = memo.values(&t).to_vec();
        key.push(matches!(*t.node(), Node::Op(LT, ..)) as u8);
        groups.entry(key).or_default().push(t);
    }
    let mut conj: Vec<(Term, Term)> = groups.values().filter(|g| g.len() > 1).flat_map(|g| g[1..].iter().map(|t2| (g[0], *t2))).collect();
    conj.sort_by_cached_key(|(a, b)| (a.show(), b.show()));
    if cap > 0 && conj.len() > cap {
        let stride = conj.len() / cap;
        conj = conj.into_iter().step_by(stride).take(cap).collect();
    }
    conj
}

/// The terms `lt` is mined over: the leaves and every operator applied to two leaves.
pub fn lt_pool(nvars: usize) -> Vec<Term> {
    let mut leaves: Vec<Term> = (0..nvars).map(Term::v).collect();
    leaves.extend([Term::ZERO, Term::ONES]);
    let mut pool = leaves.clone();
    for o in 0..5 {
        for a in &leaves {
            for b in &leaves {
                pool.push(Term::op(o, *a, *b));
            }
        }
    }
    pool
}

#[test]
pub fn lt_computes_and_its_laws_are_found_by_the_encoding_search() {
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let n = 4usize;
        // `lt_u` computes `a < b`
        let ops = ops_for(n);
        for (a, b) in [(0u128, 0u128), (3, 5), (5, 3), (7, 7), (0, 15), (15, 0), (8, 9)] {
            let e = app2(ops[5], lit(n, a), lit(n, b));
            assert_eq!(normalize(&e), normalize(&lit(1, (a < b) as u128)), "lt {a} {b}");
        }
        let v = Term::v;
        let lt = |a: Term, b: Term| Term::op(LT, a, b);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        // lt x x = lt y y; and an operand-order law with a carry on both sides
        let laws = [
            ("lt x x = lt y y", lt(Term::v(0), Term::v(0)), lt(Term::v(1), Term::v(1))),
            ("lt (and x y) (or x y) = lt (and y x) (or y x)", lt(op(1, v(0), v(1)), op(2, v(0), v(1))), lt(op(1, v(1), v(0)), op(2, v(1), v(0)))),
        ];
        for (name, t1, t2) in &laws {
            let (p, s) = add_tree_law(job, n, 2, t1, t2).unwrap_or_else(|| panic!("no proof: {name}"));
            ck(name, &p, &s);
        }
        // these hold only on the reachable carry states (the borrow of `x - 0` never becomes 1, the borrow of `x + y < x`
        // equals the add's carry): proved with lemmas conditional on a reachability invariant
        for (name, t1, t2) in [
            ("lt x 0 = lt y 0", lt(Term::v(0), Term::ZERO), lt(Term::v(1), Term::ZERO)),
            ("lt (x+y) x = lt (x+y) y", lt(op(0, v(0), v(1)), Term::v(0)), lt(op(0, v(0), v(1)), Term::v(1))),
        ] {
            let (p, s) = add_tree_law(job, n, 2, &t1, &t2).unwrap_or_else(|| panic!("no proof: {name}"));
            ck(name, &p, &s);
        }
        // false laws are not proved: by the plausibility screen, and a wrong proof would not check
        assert!(add_tree_law(job, n, 2, &lt(Term::v(0), Term::v(1)), &lt(Term::v(1), Term::v(0))).is_none());
        assert!(add_tree_law(job, n, 2, &lt(Term::v(0), Term::v(1)), &lt(Term::v(0), op(0, v(1), Term::ONES))).is_none());
    })
}

/// All `lt` pairs over the pool that agree on every width-4 input, grouped by behaviour; each conjecture is
/// built and kernel-checked.
#[test]
#[ignore]
pub fn lt_conjecture_miner() {
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let _banner = MachineBanner::start(job, "LTMINER");
        let n = 4usize;
        let nv = job.setup().or("LTMINER_VARS", 2);
        let cap = job.setup().or("LTMINER_MAX", 0);
        let pool = lt_pool(nv);
        let (mut total, mut proved, mut none) = (0, 0, 0);
        let t0 = Instant::now();
        let (mut t_law, mut t_ck) = (std::time::Duration::ZERO, std::time::Duration::ZERO);
        let conj = pool_conjectures(pool.iter().flat_map(|a| pool.iter().map(move |b| Term::op(LT, *a, *b))), n, nv, cap);
        {
            for (g0, t2) in &conj {
                let g = [*g0];
                total += 1;
                let tried = prove_checked(job, n, nv, &format!("{} = {}", g[0].show(), t2.show()), &g[0], t2);
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
        println!("LTMINER time: add_tree_law {t_law:?}, kernel check {t_ck:?}");
        println!("LTMINER {total} conjectures, {proved} proved, {none} without a proof, {:?}", t0.elapsed());
    })
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
        match *self.node() {
            Node::V(v) => out.push((v, i)),
            Node::Zero | Node::Ones => {}
            Node::Op(SHL1, a, _) => {
                if let Some(j) = i.checked_sub(1) {
                    a.pos_atoms(n, j, out);
                }
            }
            Node::Op(SHR1, a, _) => {
                if i + 1 < n {
                    a.pos_atoms(n, i + 1, out);
                }
            }
            Node::Op(_, a, b) => {
                a.pos_atoms(n, i, out);
                b.pos_atoms(n, i, out);
            }
        }
    }
    fn pos_bit(&self, n: usize, i: usize, bit: &dyn Fn(usize, usize) -> Expr) -> Expr {
        match *self.node() {
            Node::V(v) => bit(v, i),
            Node::Zero => f(),
            Node::Ones => t(),
            Node::Op(SHL1, a, _) => i.checked_sub(1).map_or_else(f, |j| a.pos_bit(n, j, bit)),
            Node::Op(SHR1, a, _) => {
                if i + 1 < n { a.pos_bit(n, i + 1, bit) } else { f() }
            }
            Node::Op(o @ 1..=3, a, b) => BIT_OPS[o - 1](a.pos_bit(n, i, bit), b.pos_bit(n, i, bit)),
            Node::Op(o, ..) => panic!("{} is not bitwise or a shift", OP_INFO[o].name),
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
                let lookup = |v: usize, j: usize| vals[atoms.iter().position(|a| *a == (v, j)).unwrap()];
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
    (0..k).fold(a, |acc, _| Term::op(if left { 6 } else { 7 }, acc, Term::ZERO))
}

#[test]
pub fn shift_ops_compute_and_shift_laws_check_and_false_ones_fail() {
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let sh = shift_k;
        let bw = |o: usize, a: Term, b: Term| Term::op(o, a, b);
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
                ("shr1 (shl1 x) = and x (shr1 (shl1 -1))", sh(1, false, sh(1, true, v(0))), bw(1, v(0), sh(1, false, sh(1, true, Term::ONES)))),
                ("xor (shl1 x) (shl1 x) = 0", bw(3, sh(1, true, v(0)), sh(1, true, v(0))), Term::ZERO),
                ("shl0 x = x", sh(0, true, v(0)), v(0)),
                ("shl n x = 0", sh(n, true, v(0)), Term::ZERO),
                ("shr n x = 0", sh(n, false, v(0)), Term::ZERO),
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
                assert!(holds(&p, &s).is_err(), "false law checked: {} = {}, n={n}", t1.show(), t2.show());
            }
        }
    })
}

/// Every pair of bitwise and shift terms over the pool that agree on all width-4 inputs, grouped by behaviour; each
/// conjecture is built and kernel-checked.
#[test]
#[ignore]
pub fn shift_conjecture_miner() {
    tatic::kernel::scoped(|| {
        let n = 4usize;
        let leaves = [Term::v(0), Term::v(1), Term::ZERO, Term::ONES];
        let mut base: Vec<Term> = leaves.to_vec();
        for a in &leaves {
            for (k, left) in [(1, true), (2, true), (1, false), (2, false)] {
                base.push(shift_k(k, left, *a));
            }
        }
        let mut pool = base.clone();
        for o in 1..=3 {
            for a in &base {
                for b in &base {
                    pool.push(Term::op(o, *a, *b));
                }
            }
        }
        let level1: Vec<Term> = pool[base.len()..].to_vec();
        for a in &level1 {
            for (k, left) in [(1, true), (1, false), (2, true)] {
                pool.push(shift_k(k, left, *a));
            }
        }
        let t0 = Instant::now();
        let conj = pool_conjectures(pool.iter().cloned(), n, 2, 0);
        for (a, b) in &conj {
            let (p, s) = bitwise_law_k(n, 2, a, b);
            ck(&format!("{} = {}", a.show(), b.show()), &p, &s);
        }
        println!("SHIFTMINER {} terms, {} conjectures proved and checked, 0 rejected, {:?}", pool.len(), conj.len(), t0.elapsed());
    })
}

#[test]
pub fn large_sums_with_shared_subterms_stay_provable() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let add = |a: Term, b: Term| Term::op(ADD, a, b);
        let s = add(add(v(0), v(1)), v(2)); // two carries
        // 8 carries on each side, under `CARRY_CAP` (a step generalizing S to a variable was removed as redundant)
        let t1 = add(s, add(s, s));
        let t2 = add(add(s, s), s);
        let (p, st) = rewrite_law(job, 2, 3, &t1, &t2).expect("proved");
        ck("add S (add S S) = add (add S S) S", &p, &st);
        // not equal: no proof
        assert!(rewrite_law(job, 2, 3, &t1, &add(add(s, s), v(0))).is_none());
    })
}

// ---- Left shifts inside machines (search note section 21): `shl1 a` is a delay cell, a carry whose next value is
// the operand's bit and whose output is the previous one, so sums with shifts are ordinary machines.

#[test]
pub fn shifts_inside_sums_are_machines_and_their_laws_check() {
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let shl = |a: Term| op(6, a, Term::ZERO);
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
            let (p, s) = add_tree_law(job, n, 2, t1, t2).unwrap_or_else(|| panic!("no proof: {name}"));
            ck(name, &p, &s);
        }
        // false laws get no proof
        assert!(add_tree_law(job, n, 2, &shl(v(0)), &v(0)).is_none());
        assert!(add_tree_law(job, n, 2, &shl(v(0)), &op(0, v(0), v(1))).is_none());
    })
}

/// The equal pairs of the `shl1` pool over `nv` variables at width 4 (leaves, shifted leaves, every operator on two of
/// them, and shifts of those), each group's first term paired with the others.
pub fn shl_conjectures(nv: usize) -> Vec<(Term, Term)> {
    let n = 4usize;
    let b = |o: usize, a: &Term, c: &Term| Term::op(o, *a, *c);
    let shl = |a: &Term| b(6, a, &Term::ZERO);
    let leaves: Vec<Term> = (0..nv).map(Term::v).chain([Term::ZERO, Term::ONES]).collect();
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
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let _banner = MachineBanner::start(job, "SHLMINER");
        let n = 4usize;
        let (nv, cap) = (job.setup().or("SHLMINER_VARS", 2), job.setup().or("SHLMINER_MAX", 0));
        let mut conj = shl_conjectures(nv);
        if cap > 0 && conj.len() > cap {
            let stride = conj.len() / cap;
            conj = conj.into_iter().step_by(stride).take(cap).collect();
        }
        let (mut total, mut proved, mut generic_none, mut t_none, mut carry_free, mut skipped, t0) = (0, 0, 0, 0, 0, 0, Instant::now());
        for (g0, t2) in &conj {
            let g = [*g0];
            {
                let big = [&g[0], t2].iter().any(|t| Machine::parse(t).is_some_and(|m| m.carries() > carry_cap(job)));
                if big {
                    skipped += 1; // beyond the carry cap of add_tree_law
                    continue;
                }
                total += 1;
                match prove_checked(job, n, nv, &format!("{} = {}", g[0].show(), t2.show()), &g[0], t2).verdict {
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
    })
}

/// `c * t` (mod 2^n) as shift-and-add: the sum of `shl1^i t` over the set bits `i` of `c`.
pub fn mul_const(c: u32, t: &Term) -> Term {
    let shl = |a: Term, k: u32| (0..k).fold(a, |acc, _| Term::op(SHL1, acc, Term::ZERO));
    let mut parts = (0..32).filter(|i| c >> i & 1 == 1).map(|i| shl(*t, i));
    let first = parts.next().expect("c is nonzero");
    parts.fold(first, |acc, p| Term::op(ADD, acc, p))
}

#[test]
pub fn multiplication_by_constants_as_shift_and_add_machines() {
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let shl = |a: Term| op(6, a, Term::ZERO);
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
            let (p, s) = add_tree_law(job, n, 2, t1, t2).unwrap_or_else(|| panic!("no proof: {name}"));
            let built = t0.elapsed();
            ck(name, &p, &s);
            println!("MUL {name}: build {built:?}, total {:?}", t0.elapsed());
        }
        // false: 3x is not 4x - 2
        assert!(add_tree_law(job, n, 2, &mul_const(3, &v(0)), &mul_const(5, &v(0))).is_none());
    })
}

/// Constant-multiplication laws (`(a + b) x`, `(a b) x`, `a (x + y)`, `(2^j - 1) x`) for constants up to `MULMINER_MAX`
/// (default 7), each proved by `add_tree_law` and kernel-checked; prints carries per side and cost, so the carry cap
/// (env `CARRY_CAP`, default 10) can be probed.
/// The constant-multiplication laws over constants up to `max`: sums, products, differences, distribution over `x+y`, `x-y`.
pub fn mul_laws(max: u32) -> Vec<(String, Term, Term)> {
    let (x, y) = (Term::v(0), Term::v(1));
    let add = |a: Term, b: Term| Term::op(ADD, a, b);
    let mut laws: Vec<(String, Term, Term)> = vec![];
    for a in 1..=max {
        for b in a..=max {
            laws.push((format!("({a}+{b})x = {a}x + {b}x"), mul_const(a + b, &x), add(mul_const(a, &x), mul_const(b, &x))));
            laws.push((format!("({a}*{b})x = {a}({b}x)"), mul_const(a * b, &x), mul_const(a, &mul_const(b, &x))));
            if b > a {
                let sub = |l: Term, r: Term| Term::op(SUB, l, r);
                laws.push((format!("({b}-{a})x = {b}x - {a}x"), mul_const(b - a, &x), sub(mul_const(b, &x), mul_const(a, &x))));
            }
        }
        let sub = |l: Term, r: Term| Term::op(SUB, l, r);
        laws.push((format!("{a}(x-y) = {a}x - {a}y"), mul_const(a, &sub(x, y)), sub(mul_const(a, &x), mul_const(a, &y))));
        laws.push((format!("{a}(x+y) = {a}x + {a}y"), mul_const(a, &add(x, y)), add(mul_const(a, &x), mul_const(a, &y))));
    }
    laws
}

#[test]
#[ignore]
pub fn mul_conjecture_miner() {
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let _banner = MachineBanner::start(job, "MULMINER");
        let max = job.setup().or("MULMINER_MAX", 7);
        let n = 4usize;
        let only = job.setup().var("MULMINER_ONLY").unwrap_or_default();
        let mut laws = mul_laws(max);
        laws.retain(|l| l.0.contains(&only));
        let (mut proved, mut none, mut capped, t0) = (0, 0, 0, Instant::now());
        for (name, t1, t2) in &laws {
            let cs = [t1, t2].map(|t| Machine::parse(t).map_or(0, |m| m.carries()));
            if !t1.is_law(t2, 2) {
                continue;
            }
            let tried = prove_checked(job, n, 2, name, t1, t2);
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
    })
}

/// Ablation audit (search note section 32): for each mul law, what a lemma-finding search would have to invent. The
/// proof's lemmas `Id(F_j, G_j(bits, phi(carries)))` are decided by case analysis once the midpoint (the phi
/// encodings and the tables `g`) is given, and the midpoint is the coarsest bisimulation, found by `moore_encoding`.
/// Prints per law: carries per side, states, classes, phi bits, table bits of `g`, the Moore time, the total time.
#[test]
#[ignore]
pub fn ablation_audit() {
    let job = &Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let _banner = MachineBanner::start(job, "AUDIT");
        let max = job.setup().or("MULMINER_MAX", 7);
        let (mut n_laws, mut moore_ns, mut total_ns) = (0, 0u128, 0u128);
        for (name, t1, t2) in mul_laws(max) {
            let (Some(m1), Some(m2)) = (Machine::parse(&t1), Machine::parse(&t2)) else { continue };
            if !t1.is_law(&t2, 2) || m1.carries().max(m2.carries()) > carry_cap(job) {
                continue;
            }
            let t = Instant::now();
            let Some(enc) = moore_encoding(&m1, &m2, 2, None) else { continue };
            let moore = t.elapsed();
            let t = Instant::now();
            let proved = add_tree_law(job, 4, 2, &t1, &t2).is_some();
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
    })
}
