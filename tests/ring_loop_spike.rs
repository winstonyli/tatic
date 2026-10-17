// Throwaway spike (docs/superpowers/specs/2026-10-10-ring-theory-prototype-spec.md, metric option E): does the mine-and-serve loop
// separate cold from seeded runs over an axiomatic commutative ring? No kernel here. A law is "proved" when a bidirectional breadth-first
// search over single axiom/lemma applications connects its two sides within a node budget; M = laws not proved within the budget.
// A lemma (a mined rule) costs one step like an axiom. Candidate lemmas are the unproved laws themselves (variables universally quantified);
// soundness is by the Z/2^64 screen only (this spike measures the metric, not soundness).
//   RING_BUDGET=1500 RING_B=30 RING_K=3 RING_ROUNDS=6 RING_SALT=1 RING_THREADS=6 cargo test --release --test ring_loop_spike -- --ignored --nocapture
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
enum T {
    V(u8),
    Z,
    O,
    Add(Box<T>, Box<T>),
    Mul(Box<T>, Box<T>),
    Neg(Box<T>),
}
use T::*;

fn add(a: T, b: T) -> T { Add(Box::new(a), Box::new(b)) }
fn mul(a: T, b: T) -> T { Mul(Box::new(a), Box::new(b)) }
fn neg(a: T) -> T { Neg(Box::new(a)) }

fn show(t: &T) -> String {
    match t {
        V(i) => ["a", "b", "c"][*i as usize].to_string(),
        Z => "0".into(),
        O => "1".into(),
        Add(a, b) => format!("({}+{})", show(a), show(b)),
        Mul(a, b) => format!("({}*{})", show(a), show(b)),
        Neg(a) => format!("-{}", show(a)),
    }
}

fn size(t: &T) -> usize {
    match t {
        Add(a, b) | Mul(a, b) => 1 + size(a) + size(b),
        Neg(a) => 1 + size(a),
        _ => 1,
    }
}

fn vars(t: &T, m: &mut u8) {
    match t {
        V(i) => *m |= 1 << i,
        Add(a, b) | Mul(a, b) => {
            vars(a, m);
            vars(b, m);
        }
        Neg(a) => vars(a, m),
        _ => {}
    }
}

fn eval(t: &T, env: &[u64; 3]) -> u64 {
    match t {
        V(i) => env[*i as usize],
        Z => 0,
        O => 1,
        Add(a, b) => eval(a, env).wrapping_add(eval(b, env)),
        Mul(a, b) => eval(a, env).wrapping_mul(eval(b, env)),
        Neg(a) => eval(a, env).wrapping_neg(),
    }
}

/// Match pattern `p` (variables = pattern variables) against `t`.
fn matches(p: &T, t: &T, b: &mut [Option<T>; 3]) -> bool {
    match (p, t) {
        (V(i), _) => match &b[*i as usize] {
            Some(x) => x == t,
            None => {
                b[*i as usize] = Some(t.clone());
                true
            }
        },
        (Z, Z) | (O, O) => true,
        (Add(a, c), Add(x, y)) | (Mul(a, c), Mul(x, y)) => matches(a, x, b) && matches(c, y, b),
        (Neg(a), Neg(x)) => matches(a, x, b),
        _ => false,
    }
}

fn subst(p: &T, b: &[Option<T>; 3]) -> T {
    match p {
        V(i) => b[*i as usize].clone().unwrap(),
        Add(x, y) => add(subst(x, b), subst(y, b)),
        Mul(x, y) => mul(subst(x, b), subst(y, b)),
        Neg(x) => neg(subst(x, b)),
        _ => p.clone(),
    }
}

type Rule = (T, T);

/// Every single-step rewrite of `t` (a rule applied at one position), with the result no larger than `cap`.
fn neighbors(t: &T, rules: &[Rule], cap: usize, out: &mut Vec<T>) {
    for (l, r) in rules {
        let mut b: [Option<T>; 3] = [None, None, None];
        if matches(l, t, &mut b) {
            let n = subst(r, &b);
            if size(&n) <= cap {
                out.push(n);
            }
        }
    }
    match t {
        Add(a, c) | Mul(a, c) => {
            let mut sub = Vec::new();
            neighbors(a, rules, cap, &mut sub);
            for x in sub {
                out.push(if matches!(t, Add(..)) { add(x, (**c).clone()) } else { mul(x, (**c).clone()) });
            }
            let mut sub = Vec::new();
            neighbors(c, rules, cap, &mut sub);
            for x in sub {
                out.push(if matches!(t, Add(..)) { add((**a).clone(), x) } else { mul((**a).clone(), x) });
            }
        }
        Neg(a) => {
            let mut sub = Vec::new();
            neighbors(a, rules, cap, &mut sub);
            out.extend(sub.into_iter().map(neg));
        }
        _ => {}
    }
}

/// Bidirectional BFS: expand the two sides alternately; proved when they share a term. Returns nodes used when proved within `budget`.
fn prove(l: &T, r: &T, rules: &[Rule], budget: usize) -> Option<usize> {
    if l == r {
        return Some(0);
    }
    let cap = size(l).max(size(r)) + 6;
    let mut seen = [HashSet::from([l.clone()]), HashSet::from([r.clone()])];
    let mut q = [VecDeque::from([l.clone()]), VecDeque::from([r.clone()])];
    let mut nodes = 0;
    let mut side = 0;
    while nodes < budget && (!q[0].is_empty() || !q[1].is_empty()) {
        if q[side].is_empty() {
            side = 1 - side;
        }
        let t = q[side].pop_front().unwrap();
        let mut ns = Vec::new();
        neighbors(&t, rules, cap, &mut ns);
        for n in ns {
            if seen[1 - side].contains(&n) {
                return Some(nodes);
            }
            if seen[side].insert(n.clone()) {
                nodes += 1;
                q[side].push_back(n);
            }
        }
        side = 1 - side;
    }
    None
}

/// Directions of the equation `l = r` that may be used as rewrites (the right side's variables must occur on the left; no bare variable on the left).
fn directed(l: &T, r: &T) -> Vec<Rule> {
    let (mut vl, mut vr) = (0, 0);
    vars(l, &mut vl);
    vars(r, &mut vr);
    let mut out = Vec::new();
    if !matches!(l, V(_)) && vr & !vl == 0 && l != r {
        out.push((l.clone(), r.clone()));
    }
    if !matches!(r, V(_)) && vl & !vr == 0 && l != r {
        out.push((r.clone(), l.clone()));
    }
    out
}

fn axioms() -> Vec<Rule> {
    let (x, y, z) = (V(0), V(1), V(2));
    let eqs = [
        (add(x.clone(), y.clone()), add(y.clone(), x.clone())),
        (add(add(x.clone(), y.clone()), z.clone()), add(x.clone(), add(y.clone(), z.clone()))),
        (mul(x.clone(), y.clone()), mul(y.clone(), x.clone())),
        (mul(mul(x.clone(), y.clone()), z.clone()), mul(x.clone(), mul(y.clone(), z.clone()))),
        (mul(x.clone(), add(y.clone(), z.clone())), add(mul(x.clone(), y.clone()), mul(x.clone(), z.clone()))),
        (add(x.clone(), Z), x.clone()),
        (mul(x.clone(), O), x.clone()),
        (add(x.clone(), neg(x.clone())), Z),
    ];
    let mut rules = Vec::new();
    for (l, r) in eqs {
        for d in directed(&l, &r) {
            if !rules.contains(&d) {
                rules.push(d);
            }
        }
    }
    rules
}

fn fnv(s: &str, salt: u64) -> u64 {
    format!("{salt}|{s}").bytes().fold(0xcbf29ce484222325u64, |h, c| (h ^ c as u64).wrapping_mul(0x100000001b3))
}

/// The law sequence: pool terms of depth <= 2 over a, b, c, 0, 1, grouped by value at 4 fixed points of Z/2^64, each group's other terms
/// paired with its first; hash-ordered by `salt`.
fn laws(salt: u64) -> Vec<(T, T)> {
    let mut out = grouped(2);
    out.sort_by_cached_key(|(a, b)| fnv(&format!("{}={}", show(a), show(b)), salt));
    out
}

/// Candidate lemmas: the true equations between terms of depth <= 1 (each term paired with the smallest of its value group).
fn small_lemmas() -> Vec<(T, T)> {
    grouped(1)
}

fn grouped(depth: usize) -> Vec<(T, T)> {
    // RING_LEAVES: which constants are leaves besides a, b, c ("01" default, "1", "0" or "")
    let k = std::env::var("RING_LEAVES").unwrap_or_else(|_| "01".into());
    let mut leaves = vec![V(0), V(1), V(2)];
    if k.contains('0') {
        leaves.push(Z);
    }
    if k.contains('1') {
        leaves.push(O);
    }
    let mut d1 = leaves.clone();
    for a in &leaves {
        d1.push(neg(a.clone()));
        for b in &leaves {
            d1.push(add(a.clone(), b.clone()));
            d1.push(mul(a.clone(), b.clone()));
        }
    }
    let mut pool = d1.clone();
    if depth >= 2 {
        for a in &d1 {
            pool.push(neg(a.clone()));
            for b in &d1 {
                pool.push(add(a.clone(), b.clone()));
                pool.push(mul(a.clone(), b.clone()));
            }
        }
    }
    let envs: [[u64; 3]; 4] = [[0x9e3779b97f4a7c15, 0xbf58476d1ce4e5b9, 0x94d049bb133111eb], [3, 5, 7], [0xdeadbeefcafef00d, 11, 0x123456789abcdef1], [1 << 63, 0xffff_ffff_ffff_fffe, 17]];
    let mut groups: HashMap<Vec<u64>, Vec<T>> = HashMap::new();
    let mut seen = HashSet::new();
    for t in pool {
        if seen.insert(t.clone()) {
            groups.entry(envs.iter().map(|e| eval(&t, e)).collect()).or_default().push(t);
        }
    }
    let mut out: Vec<(T, T)> = Vec::new();
    for g in groups.values().filter(|g| g.len() > 1) {
        let first = g.iter().min_by_key(|t| (size(t), show(t))).unwrap();
        for t in g {
            if t != first {
                out.push((first.clone(), t.clone()));
            }
        }
    }
    out.sort_by_cached_key(|(a, b)| (show(a), show(b)));
    out
}

const ENVS: [[u64; 3]; 4] = [[0x9e3779b97f4a7c15, 0xbf58476d1ce4e5b9, 0x94d049bb133111eb], [3, 5, 7], [0xdeadbeefcafef00d, 11, 0x123456789abcdef1], [1 << 63, 0xffff_ffff_ffff_fffe, 17]];

fn subterms(t: &T, out: &mut Vec<T>) {
    if !out.contains(t) {
        out.push(t.clone());
    }
    match t {
        Add(a, b) | Mul(a, b) => {
            subterms(a, out);
            subterms(b, out);
        }
        Neg(a) => subterms(a, out),
        _ => {}
    }
}

/// Candidate lemmas read off a failing law: every true equation between two distinct subterms of its two sides.
fn sub_candidates(l: &T, r: &T) -> Vec<(T, T)> {
    let mut subs = Vec::new();
    subterms(l, &mut subs);
    subterms(r, &mut subs);
    let sig = |t: &T| ENVS.iter().map(|e| eval(t, e)).collect::<Vec<_>>();
    let sigs: Vec<Vec<u64>> = subs.iter().map(sig).collect();
    let mut out = Vec::new();
    for i in 0..subs.len() {
        for j in 0..i {
            if sigs[i] == sigs[j] {
                out.push((subs[j].clone(), subs[i].clone()));
            }
        }
    }
    out
}

fn env(k: &str, d: usize) -> usize { std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d) }

fn unproved(batch: &[(T, T)], rules: &[Rule], budget: usize) -> Vec<(T, T)> {
    batch.iter().filter(|(l, r)| prove(l, r, rules, budget).is_none()).cloned().collect()
}

/// Greedy mining: candidates are the unproved laws; each round adds the lemma that proves the most of them.
fn mine(batch: &[(T, T)], small: &[(T, T)], rules: &mut Vec<Rule>, budget: usize, rounds: usize, threads: usize) {
    for _ in 0..rounds {
        let left = unproved(batch, rules, budget);
        if left.is_empty() {
            return;
        }
        // RING_CANDS: "sub" (laws + their sub-term equations), "small" (laws + the fixed depth-1 pool), "both"
        let mode = std::env::var("RING_CANDS").unwrap_or_else(|_| "small".into());
        let mut eqs: Vec<(T, T)> = left.clone();
        if mode != "sub" {
            eqs.extend(small.iter().cloned());
        }
        if mode != "small" {
            eqs.extend(left.iter().flat_map(|(l, r)| sub_candidates(l, r)));
        }
        let mut cands: Vec<Rule> = eqs.iter().flat_map(|(l, r)| directed(l, r)).filter(|c| !rules.contains(c)).collect();
        cands.sort();
        cands.dedup();
        let mut gains = vec![0usize; cands.len()];
        let next = std::sync::atomic::AtomicUsize::new(0);
        let results = std::sync::Mutex::new(&mut gains);
        std::thread::scope(|s| {
            for _ in 0..threads {
                s.spawn(|| loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if i >= cands.len() {
                        break;
                    }
                    let mut with = rules.clone();
                    with.push(cands[i].clone());
                    let g = left.iter().filter(|(l, r)| prove(l, r, &with, budget).is_some()).count();
                    results.lock().unwrap()[i] = g;
                });
            }
        });
        let (best, g) = gains.iter().enumerate().max_by_key(|(i, g)| (**g, std::cmp::Reverse(*i))).map(|(i, g)| (i, *g)).unwrap_or((0, 0));
        if g == 0 {
            return;
        }
        println!("  lemma (+{g}): {} -> {}", show(&cands[best].0), show(&cands[best].1));
        rules.push(cands[best].clone());
    }
}

/// One loop: batches of `b` laws from the stream (residue `phase` of `stride`), served under the rules so far, then mined.
fn run_loop(stream: &[(T, T)], small: &[(T, T)], phase: usize, stride: usize, b: usize, k: usize, seed: &[Rule], budget: usize, rounds: usize, threads: usize) -> (usize, Vec<usize>, usize) {
    let seq: Vec<(T, T)> = stream.iter().skip(phase).step_by(stride).take(b * k).cloned().collect();
    let mut rules = axioms();
    rules.extend(seed.iter().cloned());
    let (mut total, mut per) = (0, Vec::new());
    for r in 0..k {
        let batch = &seq[r * b..(r + 1) * b];
        let m = unproved(batch, &rules, budget).len();
        total += m;
        per.push(m);
        if r + 1 < k {
            mine(batch, small, &mut rules, budget, rounds, threads);
        }
    }
    (total, per, rules.len() - axioms().len())
}

#[test]
fn ring_prover_basics() {
    let a = axioms();
    let (x, y) = (V(0), V(1));
    // (x + 0) * 1 = x needs two rewrites
    assert!(prove(&mul(add(x.clone(), Z), O), &x, &a, 100).is_some());
    // (x*0) + y = y needs x*0 = 0, which is not an axiom (it is a lemma)
    let goal = (add(mul(x.clone(), Z), y.clone()), y.clone());
    assert!(prove(&goal.0, &goal.1, &a, 3000).is_none());
    let mut with = a.clone();
    with.extend(directed(&mul(x, Z), &Z));
    assert!(prove(&goal.0, &goal.1, &with, 3000).is_some());
    assert!(laws(1).len() > 1000);
}

#[test]
#[ignore]
fn ring_loop() {
    let (budget, b, k, rounds, salt, threads) = (env("RING_BUDGET", 1500), env("RING_B", 30), env("RING_K", 3), env("RING_ROUNDS", 6), env("RING_SALT", 1) as u64, env("RING_THREADS", 6));
    let stride = env("RING_STRIDE", 11);
    let stream = laws(salt);
    let small = small_lemmas();
    println!("candidate pool: {} small lemmas", small.len());
    println!("ring laws: {}, budget {budget}, B={b} K={k} rounds={rounds} stride={stride} salt={salt}", stream.len());
    let (m0, per0, _) = run_loop(&stream, &small, 0, stride, b, k, &[], budget, rounds, threads);
    println!("phase 0 cold: total {m0} per-batch {per0:?}");
    // seed library: a ref mine on the phase-0 stream
    let seq0: Vec<(T, T)> = stream.iter().step_by(stride).take(b * k).cloned().collect();
    let mut lib = axioms();
    let base = lib.len();
    mine(&seq0, &small, &mut lib, budget, rounds * 2, threads);
    let lib: Vec<Rule> = lib[base..].to_vec();
    println!("seed library: {} lemmas", lib.len());
    let (mut cold, mut seeded) = (0, 0);
    for phase in 1..=env("RING_STREAMS", 3) {
        let (c, pc, rc) = run_loop(&stream, &small, phase, stride, b, k, &[], budget, rounds, threads);
        let (s, ps, rs) = run_loop(&stream, &small, phase, stride, b, k, &lib, budget, rounds, threads);
        println!("stream {phase}: cold {c} {pc:?} (+{rc} lemmas) | seeded {s} {ps:?} (+{rs} lemmas)");
        cold += c;
        seeded += s;
    }
    println!("TOTAL cold {cold} seeded {seeded}");
}
