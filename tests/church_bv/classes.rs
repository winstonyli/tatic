//! The learned class table (docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md): terms over x, y, z, 0
//! and -1 to size `SIZE`, enumerated from representatives only and keyed by their values on a learned key
//! (`class_key.txt`, baked in) and their sort. A class's representative is its smallest member `Machine::parse` takes,
//! else its smallest (decision 7). `lookup` and `rep` look a term's class up; `step` and `normalize` use a replacement only with a
//! proof (§3).

use super::*;
use super::rewrite::{zip_op, Node};
use std::sync::{Mutex, OnceLock};
use crate::task::SharedMemo;

/// The operators in enumeration order; `shl1` and `shr1` are unary, enumerated with the second operand `0`.
pub const OPS: [usize; 8] = [ADD, AND, OR, XOR, SUB, SHL1, SHR1, LT];
/// The largest term size the table enumerates (decision 4).
pub const SIZE: usize = 9;
/// The key, learned by `regenerate_key` and baked in, so the table depends only on the source.
pub const KEY_FILE: &str = include_str!("class_key.txt");
const REGENERATE: &str = "<exe> classes::regenerate_key --exact --ignored --nocapture, then rebuild";

/// The table's key: per width, its inputs (x, y, z).
#[derive(Clone, Debug, PartialEq)]
pub struct Key {
    pub sets: Vec<(usize, Vec<[u128; 3]>)>,
}

impl Key {
    /// The header the build expects: its operators in order and its size.
    fn header() -> String {
        format!("ops {} size {SIZE}", OPS.map(|o| OP_INFO[o].name).join(" "))
    }

    /// A key file's inputs; an error when its header is not this build's (it was learned for another table) or a line is
    /// not `<width> <x> <y> <z>` with a width of 1 to 8.
    pub fn parse(text: &str) -> Result<Key, String> {
        let mut lines = text.lines().map(str::trim).filter(|l| !l.is_empty());
        let head = lines.next().unwrap_or("");
        if head != Key::header() {
            return Err(format!("class key header {head:?} is not {:?}: regenerate the key ({REGENERATE})", Key::header()));
        }
        let mut key = Key { sets: vec![] };
        for l in lines {
            let f: Vec<u128> = l.split_whitespace().map(str::parse).collect::<Result<_, _>>().map_err(|e| format!("class key line {l:?}: {e}"))?;
            let &[w, x, y, z] = f.as_slice() else {
                return Err(format!("class key line {l:?}: not `<width> <x> <y> <z>`"));
            };
            if !(1..=8).contains(&w) || [x, y, z].iter().any(|v| *v > low_bits(w as usize)) {
                return Err(format!("class key line {l:?}: width 1 to 8 and values within it"));
            }
            key.push(w as usize, [x, y, z]);
        }
        Ok(key)
    }

    /// The key file's text.
    pub fn text(&self) -> String {
        let mut s = Key::header() + "\n";
        for (w, ins) in &self.sets {
            for x in ins {
                s += &format!("{w} {} {} {}\n", x[0], x[1], x[2]);
            }
        }
        s
    }

    /// Adds an input at width `w`.
    pub fn push(&mut self, w: usize, x: [u128; 3]) {
        match self.sets.iter_mut().find(|s| s.0 == w) {
            Some(s) => s.1.push(x),
            None => self.sets.push((w, vec![x])),
        }
    }

    /// The refinement's start: the 8 tuples of 0s and 1s, at width 8.
    pub fn start() -> Key {
        let mut k = Key { sets: vec![] };
        for i in 0..8u128 {
            k.push(8, [0, 1, 2].map(|v| i >> v & 1));
        }
        k
    }

    /// Inputs over all widths.
    pub fn len(&self) -> usize {
        self.sets.iter().map(|s| s.1.len()).sum()
    }
}

/// A key file's text reads back as the same key, and the baked-in file parses.
#[test]
fn a_key_round_trips_through_its_text() {
    let mut k = Key::start();
    k.push(4, [15, 0, 7]);
    k.push(3, [1, 2, 3]);
    assert_eq!(Key::parse(&k.text()), Ok(k.clone()));
    assert_eq!(k.len(), 10);
    assert!(Key::parse(KEY_FILE).is_ok(), "{:?}", Key::parse(KEY_FILE).err());
}

/// A key learned for another operator set or size, or a malformed line, is refused with the regeneration command.
#[test]
fn a_key_with_another_header_names_the_regeneration() {
    let other_ops = Key::start().text().replacen(" lt size", " size", 1);
    let other_size = Key::start().text().replacen("size 9", "size 11", 1);
    for text in [other_ops, other_size] {
        let e = Key::parse(&text).unwrap_err();
        assert!(e.contains("classes::regenerate_key"), "{e}");
    }
    let head = Key::start().text().lines().next().unwrap().to_string();
    assert!(Key::parse(&format!("{head}\n8 1 2\n")).is_err(), "three fields");
    assert!(Key::parse(&format!("{head}\n4 16 0 0\n")).is_err(), "a value wider than its width");
    assert!(Key::parse(&format!("{head}\n9 0 0 0\n")).is_err(), "width 9");
}

/// Built from the key file to size 5 (spec "Testing"): padding maps to its leaf, value-equal two-leaf nodes (the
/// old twin filter's classes) share a representative, a unary operator's ignored operand becomes `0`, and an `lt` whose first member the
/// machine refuses is represented by a later one it takes (decision 7: both size 5, the `shr1` one enumerated first).
#[test]
fn the_size_5_table_maps_terms_to_their_representatives() {
    let (c, _) = Classes::build(&Key::parse(KEY_FILE).unwrap(), 5, 0, 0);
    let n = |s: &str| c.canonical(&parse_term(s)).show();
    assert_eq!(n("sub(y, y)"), "0");
    assert_eq!(n("add(x, 0)"), "x");
    assert_eq!(n("sub(-1, x)"), "xor(x, -1)");
    assert_eq!(n("xor(x, -1)"), "xor(x, -1)");
    assert_eq!(n("shr1(x, y)"), "shr1(x, 0)");
    assert_eq!(n("lt(0, shr1(x, 0))"), "lt(sub(0, -1), x)");
    let rep = |s: &str| c.rep(&parse_term(s)).map(|t| t.show());
    assert_eq!(rep("add(x, 0)").as_deref(), Some("x"));
    assert_eq!(rep("x"), None, "a representative maps to nothing");
    assert_eq!(rep("add(u, 0)"), None, "a fourth variable");
}

/// Every stored representative is a fixpoint below its root (spec §5): no proper subterm is one the table replaces, a
/// displaced representative included (docs/tier-cycle.md, "Displaced representatives stay inside stored ones").
#[test]
fn representatives_are_fixpoints_below_the_root() {
    fn subterms(t: &Term, out: &mut Vec<Term>) {
        if let Node::Op(_, a, b) = *t.node() {
            for s in [a, b] {
                out.push(s);
                subterms(&s, out);
            }
        }
    }
    let (c, _) = Classes::build(&Key::parse(KEY_FILE).unwrap(), SIZE, 0, 0);
    let reps: Vec<Term> = c.map.values().copied().collect();
    let held: Vec<String> = reps
        .iter()
        .filter_map(|r| {
            let mut s = vec![];
            subterms(r, &mut s);
            s.iter().find_map(|u| c.rep(u).map(|n| format!("{} holds {} -> {}", r.show(), u.show(), n.show())))
        })
        .collect();
    assert!(held.is_empty(), "{} representatives hold a replaced subterm, e.g. {:?}", held.len(), &held[..held.len().min(3)]);
}

/// The full table from the key file, pinned: its counts and a fingerprint of its representatives (not of `class_hash`'s
/// keys), so a change to how the build computes or hashes values (not what they are) leaves the table as it was.
#[test]
fn the_full_table_is_pinned() {
    use std::hash::{Hash, Hasher};
    let (c, st) = Classes::build(&Key::parse(KEY_FILE).unwrap(), SIZE, 0, 0);
    let print = c.map.values().fold(0u64, |acc, r| {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        r.show().hash(&mut h);
        acc ^ h.finish()
    });
    assert_eq!((c.len(), st.lts, st.merges, st.displaced, print), (341866, 95616, 647669, 798, 6359512567973285473));
}

/// A class's key: a term's values on the key's inputs (all widths end to end) and whether it is an `lt` (a second sort),
/// hashed to 128 bits (SipHash: foldhash on fixed seeds built no faster, docs/tier-cycle.md, "What a build spends").
fn class_hash(vals: &[u8], lt: bool) -> (u64, u64) {
    use std::hash::{Hash, Hasher};
    let (mut h1, mut h2) = (std::collections::hash_map::DefaultHasher::new(), std::collections::hash_map::DefaultHasher::new());
    (lt, vals).hash(&mut h1);
    (0xa5u8, vals, lt).hash(&mut h2);
    (h1.finish(), h2.finish())
}

/// The table: each class's key to its representative, and the lookup's memos: values (one per key width, in key order)
/// and `rep`'s answers, so a term's 432 values are gathered and hashed once per process (run 2026-10-23-phase1-prof).
pub struct Classes {
    map: hashbrown::HashMap<(u64, u64), Term>,
    memos: Mutex<(Vec<ValueMemo<u8>>, hashbrown::HashMap<Term, Option<Term>>)>,
}

/// What a build saw besides the table: the merges the key proposed (a new term whose key a class already has), a uniform
/// sample of them as (member, its class's representative when the build ends), the representatives a later member
/// displaced (decision 7), the `lt` classes, and the build's time.
pub struct BuildStats {
    pub merges: usize,
    pub sample: Vec<(Term, Term)>,
    pub displaced: usize,
    pub lts: usize,
    pub millis: u128,
}

/// The process's table, built on first use from the baked-in key.
static CLASSES: OnceLock<Classes> = OnceLock::new();

impl Classes {
    /// The table to `size` under `key`, from representatives only, with a reservoir sample of `sample_n` merges (`seed`
    /// drives it). The terms' values live only while it builds.
    pub fn build(key: &Key, size: usize, sample_n: usize, mut seed: u128) -> (Classes, BuildStats) {
        let t0 = std::time::Instant::now();
        // the key's inputs end to end, one run per width: (where it starts, its mask), then the end
        let (mut runs, mut cols) = (vec![], [vec![], vec![], vec![]]);
        for (w, ins) in &key.sets {
            runs.push((cols[0].len(), low_bits(*w)));
            for x in ins {
                for v in 0..3 {
                    cols[v].push(x[v] as u8);
                }
            }
        }
        let len = cols[0].len();
        runs.push((len, 0));
        let leaf = |t: &Term| -> Vec<u8> {
            match *t.node() {
                Node::V(v) => cols[v].clone(),
                Node::Zero => vec![0; len],
                _ => runs.windows(2).flat_map(|r| std::iter::repeat_n(r[0].1 as u8, r[1].0 - r[0].0)).collect(),
            }
        };
        // a run at a time, so each loop has its operator and mask fixed (called per element through `OP_INFO[o].word` it
        // was 65% of a build: docs/tier-cycle.md, "What a build spends")
        let zip = |o: usize, out: &mut [u8], a: &[u8], b: &[u8]| {
            for r in runs.windows(2) {
                let s = r[0].0..r[1].0;
                zip_op(o, &mut out[s.clone()], &a[s.clone()], &b[s], r[0].1);
            }
        };
        // a candidate's values, copied out only for a new class
        let mut buf = vec![0u8; len];
        let mut map: hashbrown::HashMap<(u64, u64), Term> = Default::default();
        let mut st = BuildStats { merges: 0, sample: vec![], displaced: 0, lts: 0, millis: 0 };
        // representatives a later member displaced, to the member: the sample's pairs are fixed up from it at the end
        let mut moved: hashbrown::HashMap<Term, Term> = Default::default();
        // per size, the bit-vector representatives and their values (an `lt` is a sort no operator takes)
        let mut reps: Vec<Vec<(Term, Vec<u8>)>> = vec![vec![]; size + 1];
        for t in [Term::v(0), Term::v(1), Term::v(2), Term::ZERO, Term::ONES] {
            let (v, h) = (leaf(&t), class_hash(&leaf(&t), false));
            if !map.contains_key(&h) {
                map.insert(h, t);
                reps[1].push((t, v));
            }
        }
        for s in (3..=size).step_by(2) {
            let (done, rest) = reps.split_at_mut(s);
            let new = &mut rest[0];
            for sa in (1..s - 1).step_by(2) {
                let sb = s - 1 - sa;
                for (ra, va) in &done[sa] {
                    for (rb, vb) in &done[sb] {
                        for o in OPS {
                            if OP_INFO[o].shift && *rb != Term::ZERO {
                                continue;
                            }
                            zip(o, &mut buf, va, vb);
                            let h = class_hash(&buf, o == LT);
                            // made only when needed: most candidates are merges, and interned terms are never freed
                            let term = || Term::op(o, *ra, *rb);
                            match map.get_mut(&h) {
                                Some(rep) => {
                                    if Machine::parse(rep).is_none() && Machine::parse(&term()).is_some() {
                                        moved.insert(*rep, term());
                                        *rep = term();
                                        st.displaced += 1;
                                    }
                                    st.merges += 1;
                                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                                    let slot = if st.sample.len() < sample_n { Some(st.sample.len()) } else { Some((seed >> 64) as usize % st.merges).filter(|&x| x < sample_n) };
                                    if let Some(x) = slot {
                                        let c = (term(), *rep);
                                        if x == st.sample.len() {
                                            st.sample.push(c);
                                        } else {
                                            st.sample[x] = c;
                                        }
                                    }
                                }
                                None => {
                                    map.insert(h, term());
                                    if o == LT {
                                        st.lts += 1;
                                    } else {
                                        new.push((term(), buf.clone()));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        drop(reps);
        // a displaced representative stays inside the representatives built over it, at sizes its successor (larger) could
        // not reach: put the successor there, so each is a fixpoint below its root (spec §5; values unchanged, a term may
        // pass `size`; docs/tier-cycle.md, "Displaced representatives stay inside stored ones"). A successor holds no
        // displaced term (it parses, so its subterms do), so one pass is enough.
        fn subst(t: Term, moved: &hashbrown::HashMap<Term, Term>) -> Term {
            if let Some(&n) = moved.get(&t) {
                return n;
            }
            match *t.node() {
                Node::Op(o, a, b) => {
                    let (a1, b1) = (subst(a, moved), subst(b, moved));
                    if (a1, b1) == (a, b) { t } else { Term::op(o, a1, b1) }
                }
                _ => t,
            }
        }
        for r in map.values_mut() {
            *r = subst(*r, &moved);
        }
        // a sampled pair's representative as the build ends: a displaced one is now a member
        for (u, r) in st.sample.iter_mut() {
            if let Some(&n) = moved.get(r) {
                (*u, *r) = if *u == n { (*r, n) } else { (*u, n) };
            }
            *r = subst(*r, &moved);
        }
        let memos = key.sets.iter().map(|(w, ins)| ValueMemo::new(*w, ins.len(), (0..3).map(|v| ins.iter().map(|x| x[v] as u8).collect()).collect())).collect();
        st.millis = t0.elapsed().as_millis();
        (Classes { map, memos: Mutex::new((memos, Default::default())) }, st)
    }

    /// The process's table, built from `KEY_FILE` on first use; a key learned for another table fails the process.
    pub fn get() -> &'static Classes {
        CLASSES.get_or_init(|| {
            let key = Key::parse(KEY_FILE).unwrap_or_else(|e| panic!("{e}"));
            let (c, st) = Classes::build(&key, SIZE, 0, 0);
            println!("CLASSES {} classes ({} lt) to size {SIZE} under {} key inputs, built in {} ms", c.len(), st.lts, key.len(), st.millis);
            // the build's values go back to the system (spec §1, plan R9: commit 191 MB to 72 MB with large OS pages off,
            // as sweep children run; none returned with them on, 257 MB; run 2026-10-23-class-commit)
            unsafe extern "C" {
                fn mi_collect(force: bool);
            }
            unsafe { mi_collect(true) };
            c
        })
    }

    /// Classes in the table.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// The representative of `t`'s class, `t` itself included, when the table knows the class; `None` otherwise, and for
    /// a term over a variable other than x, y, z. Pure: no proof. One memo holds every term asked (spec §5).
    pub fn lookup(&self, t: &Term) -> Option<Term> {
        if t.max_var() >= 3 {
            return None;
        }
        let (values, reps) = &mut *self.memos.lock().unwrap_or_else(|e| e.into_inner());
        *reps.entry(*t).or_insert_with(|| {
            let mut vals = vec![];
            for m in values.iter_mut() {
                vals.extend_from_slice(m.values(t));
            }
            self.map.get(&class_hash(&vals, matches!(*t.node(), Node::Op(LT, ..)))).copied()
        })
    }

    /// The representative of `t`'s class when the table knows it and it is not `t` (`lookup`, the term itself left out).
    pub fn rep(&self, t: &Term) -> Option<Term> {
        self.lookup(t).filter(|r| r != t)
    }

    /// Every stored representative (the streams' seeds, spec §9).
    pub fn reps(&self) -> impl Iterator<Item = Term> + '_ {
        self.map.values().copied()
    }

    /// Terms in the process's lookup memo, or `None` before the table is built (it is not built here): the worker prints
    /// it after each task, so a gate reads the memo's peak (spec §9).
    pub fn memo_len() -> Option<usize> {
        CLASSES.get().map(|c| c.memos.lock().unwrap_or_else(|e| e.into_inner()).1.len())
    }

    /// `t` with every node, bottom-up, replaced by its class's representative where the table knows it (no proof: the law
    /// generator's twin filter).
    pub fn canonical(&self, t: &Term) -> Term {
        let t1 = match *t.node() {
            Node::Op(o, a, b) => Term::op(o, self.canonical(&a), self.canonical(&b)),
            _ => *t,
        };
        self.rep(&t1).unwrap_or(t1)
    }
}

/// How a replacement `u -> r` is proved (spec §3, R2, R3): its prover, the law's sides over `V(0..)` and its arguments.
#[derive(Clone)]
struct Verdict {
    kind: LawKind,
    lhs: Term,
    rhs: Term,
    args: Vec<Term>,
}

/// Replacements' verdicts by (width, carry cap, u, r). Pure: a verdict depends only on its key (`tree_encoding` reads the
/// carry cap before its own memo).
static VERDICTS: SharedMemo<(usize, usize, Term, Term), Option<Verdict>> = SharedMemo::new();

/// The verdict on `u -> r` at width `n`: `Bitwise` when neither side has `add`, `sub` or `lt` and they agree at widths
/// 1..=5; else `Tree` when `tree_encoding` finds a carry encoding with each `shr1` node a fresh variable (decision 3);
/// else none (decision 6).
fn verdict(job: &Job, n: usize, u: &Term, r: &Term) -> Option<Verdict> {
    let kv = 1 + u.max_var().max(r.max_var());
    let vars = (0..kv).map(Term::v);
    if u.add_free() && r.add_free() {
        // a position reads only a few neighbours, so these widths hold every case (`prove_eq`'s per-position step)
        let holds = (1..=5usize).all(|w| {
            (0..1u128 << (w * kv)).all(|i| {
                let x: Vec<u128> = (0..kv).map(|v| (i >> (w * v)) & low_bits(w)).collect();
                u.interp(w, &x) == r.interp(w, &x)
            })
        });
        return holds.then(|| Verdict { kind: LawKind::Bitwise, lhs: *u, rhs: *r, args: vars.collect() });
    }
    fn atomize(t: Term, kv: usize, atoms: &mut Vec<Term>) -> Term {
        match *t.node() {
            Node::Op(SHR1, ..) => {
                let i = atoms.iter().position(|a| *a == t).unwrap_or_else(|| {
                    atoms.push(t);
                    atoms.len() - 1
                });
                Term::v(kv + i)
            }
            Node::Op(o, a, b) => Term::op(o, atomize(a, kv, atoms), atomize(b, kv, atoms)),
            _ => t,
        }
    }
    let mut atoms = vec![];
    let (lhs, rhs) = (atomize(*u, kv, &mut atoms), atomize(*r, kv, &mut atoms));
    let args: Vec<Term> = vars.chain(atoms).collect();
    tree_encoding(job, n, args.len(), &lhs, &rhs)?;
    Some(Verdict { kind: LawKind::Tree, lhs, rhs, args })
}

impl Classes {
    /// `rep(t)` when that replacement has a proof at width `n` and its representative is over the context's `k` variables,
    /// with its plan (`Plan::Law`, or the shared `Plan::Counting` while counting); counted in `job.table_steps`.
    pub fn step(&self, job: &mut Job, n: usize, k: usize, t: &Term) -> Option<(Term, PlanRc)> {
        let r = self.rep(t)?;
        if r.max_var() >= k {
            return None;
        }
        let key = (n, carry_cap(job), *t, r);
        let v = match VERDICTS.get(&key) {
            Some(v) => v,
            None => {
                let v = verdict(job, n, t, &r);
                if VERDICTS.insert(key, v.clone()) && v.is_none() {
                    println!("CLASS_UNUSABLE {} = {}", t.show(), r.show());
                }
                v
            }
        }?;
        job.table_steps.insert((*t, r));
        Some((r, Plan::law(job, v.kind, v.lhs, v.rhs, v.args)))
    }

    /// `t` with `step` taken at every node, bottom-up, and its plan: `Cong` per changed node, `Trans` per replacement.
    pub fn normalize(&self, job: &mut Job, n: usize, k: usize, t: &Term) -> (Term, PlanRc) {
        let (t1, p1) = match *t.node() {
            Node::Op(o, a, b) => {
                let ((a1, pa), (b1, pb)) = (self.normalize(job, n, k, &a), self.normalize(job, n, k, &b));
                if (a1, b1) == (a, b) { (*t, Plan::refl(job, t)) } else { (Term::op(o, a1, b1), Plan::cong(job, o, pa, pb)) }
            }
            _ => (*t, Plan::refl(job, t)),
        };
        match self.step(job, n, k, &t1) {
            Some((r, p)) => (r, Plan::trans(job, p1, p)),
            None => (t1, p1),
        }
    }
}

/// The key refinement's refuter (R8 of the plan): 4096 pseudo-random width-8 inputs, every width-4 input, every width-3
/// input, then the screen's width-8 inputs.
struct Refuter {
    r8: ValueMemo<u8>,
    e4: ValueMemo<u8>,
    e3: ValueMemo<u8>,
}

impl Refuter {
    const TESTS: usize = 4096;
    fn new() -> Refuter {
        let mut seed = 0x6a09_e667_f3bc_c908u128;
        let tvars: Vec<Box<[u8]>> = (0..3)
            .map(|_| {
                (0..Self::TESTS)
                    .map(|_| {
                        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                        (seed >> 40) as u8
                    })
                    .collect()
            })
            .collect();
        Refuter { r8: ValueMemo::new(8, Self::TESTS, tvars), e4: ValueMemo::exhaustive(4, 3), e3: ValueMemo::exhaustive(3, 3) }
    }

    /// An input on which `a` and `b` differ: (width, tuple).
    fn refute(&mut self, a: &Term, b: &Term) -> Option<(usize, [u128; 3])> {
        let tuple = |v: Vec<u128>| [v[0], v[1], v[2]];
        if let Some(i) = self.r8.first_difference(a, b, Self::TESTS) {
            return Some((8, tuple(self.r8.input(i))));
        }
        if let Some(i) = self.e4.first_difference(a, b, 1 << 12) {
            return Some((4, tuple(self.e4.input(i))));
        }
        if let Some(i) = self.e3.first_difference(a, b, 1 << 9) {
            return Some((3, tuple(self.e3.input(i))));
        }
        a.counterexample(b, 8, 3).map(|x| (8, tuple(x)))
    }
}

/// Regenerates `class_key.txt` (spec §2; run `2026-10-22-key-refine`): from the 8 tuples of 0s and 1s, each round builds
/// the table, refutes a sample of 20000 of its merges, and adds one refuting input per refuted merge that the inputs added
/// this round do not already separate. The file is written only on a round whose sample has no refuted merge; rebuild to
/// use it.
#[test]
#[ignore]
fn regenerate_key() {
    let mut key = Key::start();
    for round in 0..30u128 {
        let (c, st) = Classes::build(&key, SIZE, 20000, 0x51ed_270b_27a3_c1f5 + round);
        // the memos grow with every term refuted, so each thousand pairs starts fresh ones
        let mut refuter = Refuter::new();
        let (mut refuted, mut added) = (0usize, Vec::<(usize, [u128; 3])>::new());
        for (i, (u, r)) in st.sample.iter().enumerate() {
            if i % 1000 == 999 {
                refuter = Refuter::new();
            }
            if let Some(cex) = refuter.refute(u, r) {
                refuted += 1;
                if !added.iter().any(|(w, x)| u.interp(*w, x) != r.interp(*w, x)) {
                    added.push(cex);
                }
            }
        }
        println!(
            "ROUND {round}: key {} inputs, {} classes ({} lt), {} merges, {} displaced, refuted {refuted} of {}, added {}, build {} ms",
            key.len(),
            c.len(),
            st.lts,
            st.merges,
            st.displaced,
            st.sample.len(),
            added.len(),
            st.millis
        );
        if refuted == 0 {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/church_bv/class_key.txt");
            std::fs::write(&path, key.text()).unwrap();
            println!("WROTE {} ({} inputs: {})", path.display(), key.len(), key.sets.iter().map(|(w, i)| format!("{} at width {w}", i.len())).collect::<Vec<_>>().join(", "));
            return;
        }
        for (w, x) in added {
            key.push(w, x);
        }
    }
    panic!("the key did not converge in 30 rounds; class_key.txt is unchanged");
}

/// A step's replacement has a plan that compiles to a kernel-checked proof at width 4: an `add` law (`Tree`), a bitwise
/// law (`Bitwise`), one over a `shr1` atom, and `shr1` with a nonzero ignored operand.
#[test]
fn steps_compile_to_checked_proofs() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let c = Classes::get();
        for (s, want) in [("sub(add(x, y), y)", "x"), ("and(x, or(x, y))", "x"), ("add(shr1(x, 0), 0)", "shr1(x, 0)"), ("shr1(x, y)", "shr1(x, 0)")] {
            let t = parse_term(s);
            let (r, plan) = c.step(job, 4, 3, &t).unwrap_or_else(|| panic!("{s}: no step"));
            assert_eq!(r.show(), want);
            let (p, st) = law_proof(job, 4, 3, &t, &r, &plan);
            job.lemmas.ck(s, &p, &st);
        }
        assert_eq!(job.table_steps.len(), 4);
    });
}

/// Counting takes the same steps (the verdict is decided the same way, R3) and builds no plan; the law it closes then
/// compiles to a checked proof (spec "Testing": counting and compiling agree).
#[test]
fn counting_and_compiling_agree() {
    let (a, b) = (parse_term("add(sub(add(x, y), y), and(z, or(z, x)))"), parse_term("add(and(x, or(x, y)), z)"));
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let c = Classes::get();
        let rules = job.rules().counting(true);
        let (na, nb, plan) = job.with_rules(rules, |job| {
            let ((na, pa), (nb, _)) = (c.normalize(job, 4, 3, &a), c.normalize(job, 4, 3, &b));
            (na, nb, pa)
        });
        assert!(matches!(*plan, Plan::Counting));
        assert_eq!(na.show(), nb.show(), "the law meets while counting");
        let ((ma, pa), (mb, pb)) = (c.normalize(job, 4, 3, &a), c.normalize(job, 4, 3, &b));
        assert_eq!((ma.show(), mb.show()), (na.show(), nb.show()));
        let plan = Plan::trans(job, pa, Plan::sym(job, pb));
        let (p, s) = law_proof(job, 4, 3, &a, &b, &plan);
        job.lemmas.ck("counted law", &p, &s);
    });
}

/// A representative over a variable the context lacks is not used (R2): `add(y, 0)` steps to `y` with two variables, not
/// with one.
#[test]
fn a_representative_outside_the_context_is_not_used() {
    let job = &mut Job::new(Setup::process());
    let c = Classes::get();
    let t = parse_term("add(y, 0)");
    assert_eq!(c.step(job, 4, 2, &t).map(|(r, _)| r.show()).as_deref(), Some("y"));
    assert!(c.step(job, 4, 1, &t).is_none());
}

/// Every replacement the table makes on the held-out laws (spec "Testing", "Proofs"; `docs/runs/2026-10-23/fixtures/held`,
/// from runs `2026-10-22-size-band` and `-join-residue`) has a verdict at width 4, and every law that meets compiles to a
/// kernel-checked proof. Prints the laws met per file, the replacements by prover, and the time in verdicts and in proofs.
#[test]
#[ignore]
fn held_out_replacements_prove() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/runs/2026-10-23/fixtures/held");
    let mut files: Vec<_> = std::fs::read_dir(&dir).unwrap().flatten().map(|e| e.path()).collect();
    files.sort();
    let c = Classes::get();
    // the replacements canonicalizing makes (the table's own choice, before any verdict)
    fn walk(c: &Classes, t: &Term, out: &mut hashbrown::HashSet<(Term, Term)>) -> Term {
        let t1 = match *t.node() {
            Node::Op(o, a, b) => Term::op(o, walk(c, &a, out), walk(c, &b, out)),
            _ => *t,
        };
        match c.rep(&t1) {
            Some(r) => {
                out.insert((t1, r));
                r
            }
            None => t1,
        }
    }
    let mut laws: Vec<(String, Term, Term)> = vec![];
    let mut pairs = hashbrown::HashSet::new();
    for f in &files {
        let (mut n, mut met) = (0, 0);
        for line in std::fs::read_to_string(f).unwrap().lines().filter(|l| l.contains(" = ")) {
            let (l, r) = line.split_once(" = ").unwrap();
            let (a, b) = (parse_term(l.trim()), parse_term(r.trim()));
            n += 1;
            if walk(c, &a, &mut pairs) == walk(c, &b, &mut pairs) {
                met += 1;
                laws.push((line.to_string(), a, b));
            }
        }
        println!("LAWS {}: {met} of {n} meet", f.file_name().unwrap().to_string_lossy());
    }
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let t0 = std::time::Instant::now();
        let mut pairs: Vec<_> = pairs.into_iter().collect();
        pairs.sort_by_cached_key(|(u, r)| (u.show(), r.show()));
        let unusable: Vec<String> = pairs.iter().filter(|(u, _)| c.step(job, 4, 3, u).is_none()).map(|(u, r)| format!("{} = {}", u.show(), r.show())).collect();
        let verdict_ms = t0.elapsed().as_millis();
        // a replacement with no proof leaves `normalize` short of `walk`'s normal form, so a met law would not compile
        assert!(unusable.is_empty(), "{} of {} replacements with no proof: {unusable:?}", unusable.len(), pairs.len());
        let t1 = std::time::Instant::now();
        for (line, a, b) in &laws {
            let ((_, pa), (_, pb)) = (c.normalize(job, 4, 3, a), c.normalize(job, 4, 3, b));
            let plan = Plan::trans(job, pa, Plan::sym(job, pb));
            let (p, s) = law_proof(job, 4, 3, a, b, &plan);
            job.lemmas.ck(line, &p, &s);
        }
        println!("REPLACEMENTS {} made, all with a proof; verdicts {verdict_ms} ms, {} laws compiled and checked in {} ms", pairs.len(), laws.len(), t1.elapsed().as_millis());
    });
}

/// Phase 1 (spec §4): the table closes a law the join left at 20000 visits (run `2026-10-22-join-residue`) with no
/// machine proof, and the proof checks; with `ABLATE=classes,eq_classes` the law takes the old path (a machine proof, or none).
#[test]
fn prove_eq_closes_a_residue_law_by_the_table() {
    let (a, b) = (parse_term("add(and(z, xor(x, -1)), y)"), parse_term("add(xor(x, and(xor(x, -1), z)), sub(y, x))"));
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let plan = prove_eq(job, 4, 3, &a, &b).expect("closed by the table");
        assert_eq!(job.rw.fallbacks, 0);
        assert!(!job.table_steps.is_empty());
        let (p, s) = law_proof(job, 4, 3, &a, &b, &plan);
        job.lemmas.ck("residue law", &p, &s);
    });
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes,eq_classes".into())]));
    let r = prove_eq(job, 4, 3, &a, &b);
    assert!(job.table_steps.is_empty(), "the ablated path takes no table step");
    assert!(r.is_none() || job.rw.fallbacks > 0, "without the table the law needs the machine or stays open");
}

/// A pair whose normal forms differ keeps none of the table steps taken on it (`Job::steps_if_closed`, as the
/// kernel-check task counts): `sub(add(x, y), y)` steps to `x`, which does not meet `y`.
#[test]
fn steps_of_a_pair_left_open_are_not_counted() {
    let (a, b) = (parse_term("sub(add(x, y), y)"), parse_term("y"));
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        assert!(Classes::get().step(job, 4, 3, &a).is_some());
        job.table_steps.clear();
        assert!(job.steps_if_closed(|job| prove_eq(job, 4, 3, &a, &b)).is_none());
        assert!(job.table_steps.is_empty(), "{} steps counted", job.table_steps.len());
    });
}

/// `lookup` answers a known class with its representative, the term itself included; `rep` only when it differs; a
/// term over a fourth variable is unknown.
#[test]
fn lookup_includes_the_term_itself() {
    let (c, _) = Classes::build(&Key::parse(KEY_FILE).unwrap(), 5, 0, 0);
    let show = |t: Option<Term>| t.map(|t| t.show());
    let x = parse_term("x");
    assert_eq!(show(c.lookup(&x)), Some("x".to_string()));
    assert_eq!(show(c.rep(&x)), None);
    assert_eq!(show(c.lookup(&parse_term("sub(y, y)"))), Some("0".to_string()));
    assert_eq!(show(c.lookup(&parse_term("add(x, u)"))), None);
}

/// Phase 2 (spec §5): a node the table knows is final in `rewrite`. `sub(add(x, y), y)` rewrites to `x` with no rule
/// tried (the rule trace stays empty) and a table step counted; with `ABLATE=classes,eq_classes` rules are tried and
/// no table step is taken.
#[test]
fn rewrite_takes_the_table_before_any_rule() {
    let t = parse_term("sub(add(x, y), y)");
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        job.rw.trace = Some(vec![]);
        let (r, _) = rewrite(job, &t, 4, 3);
        assert_eq!(r.show(), "x");
        assert_eq!(job.rw.trace.as_ref().unwrap().len(), 0, "a rule was tried");
        assert!(!job.table_steps.is_empty());
    });
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes,eq_classes".into())]));
    tatic::kernel::scoped(|| {
        job.rw.trace = Some(vec![]);
        rewrite(job, &t, 4, 3);
        assert!(!job.rw.trace.as_ref().unwrap().is_empty(), "no rule was tried");
        assert!(job.table_steps.is_empty());
    });
}

/// A node over a fourth variable is unknown to the table: `sub(add(x, u), u)` goes to the rules (the trace records
/// them) and no table step is taken at a node with `u`.
#[test]
fn rewrite_leaves_a_fourth_variable_to_the_rules() {
    let t = parse_term("sub(add(x, u), u)");
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        job.rw.trace = Some(vec![]);
        let (r, _) = rewrite(job, &t, 4, 4);
        assert_eq!(r.show(), "x");
        assert!(!job.rw.trace.as_ref().unwrap().is_empty());
        assert!(job.table_steps.iter().all(|(u, _)| !u.has_var(3)));
    });
}

/// Review Focus 1: a node past the table's size whose values match a stored class is replaced only through `step`'s
/// verdict. `add(add(add(x, y), z), add(add(x, z), y))` (size 11, children normal) has the class of a term within size
/// 9; it is replaced, and the replacement is a counted (proved) step from a node larger than `SIZE`.
#[test]
fn rewrite_replaces_a_node_past_the_table_only_with_a_proof() {
    let t = parse_term("add(add(add(x, y), z), add(add(x, z), y))");
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let (r, plan) = rewrite(job, &t, 4, 3);
        assert!(r.size() <= SIZE, "{}", r.show());
        assert!(job.table_steps.iter().any(|(u, _)| u.size() > SIZE), "no counted step from a node past the table's size");
        let (p, s) = law_proof(job, 4, 3, &t, &r, &plan);
        job.lemmas.ck("past the table's size", &p, &s);
    });
}
