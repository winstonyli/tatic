//! The learned class table (docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md): terms over x, y, z, 0
//! and -1 to size `SIZE`, enumerated from representatives only and keyed by their values on a learned key
//! (`class_key.txt`, baked in) and their sort. A class's representative is its smallest member `Machine::parse` takes,
//! else its smallest (decision 7). `rep` looks a term's class up; `step` and `normalize` use a replacement only with a
//! proof (§3).

use super::*;
use super::rewrite::Node;
use std::sync::{Mutex, OnceLock};

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

/// Built from the key file to size 5 (spec "Testing"): padding maps to its leaf, `ClassReps`'s value-equal two-leaf
/// nodes share a representative, a unary operator's ignored operand becomes `0`, and an `lt` whose first member the
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

/// A class's key: a term's values on the key's inputs (all widths end to end) and whether it is an `lt` (a second sort),
/// hashed to 128 bits.
fn class_hash(vals: &[u8], lt: bool) -> (u64, u64) {
    use std::hash::{Hash, Hasher};
    let (mut h1, mut h2) = (std::collections::hash_map::DefaultHasher::new(), std::collections::hash_map::DefaultHasher::new());
    (lt, vals).hash(&mut h1);
    (0xa5u8, vals, lt).hash(&mut h2);
    (h1.finish(), h2.finish())
}

/// The table: each class's key to its representative, and the lookup's value memos (one per key width, in key order).
pub struct Classes {
    map: hashbrown::HashMap<(u64, u64), Term>,
    memos: Mutex<Vec<ValueMemo<u8>>>,
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
        let (mut masks, mut cols) = (vec![], [vec![], vec![], vec![]]);
        for (w, ins) in &key.sets {
            for x in ins {
                masks.push(low_bits(*w));
                for v in 0..3 {
                    cols[v].push(x[v] as u8);
                }
            }
        }
        let leaf = |t: &Term| -> Vec<u8> {
            match *t.node() {
                Node::V(v) => cols[v].clone(),
                Node::Zero => vec![0; masks.len()],
                _ => masks.iter().map(|m| *m as u8).collect(),
            }
        };
        let zip = |o: usize, a: &[u8], b: &[u8]| -> Vec<u8> {
            let f = OP_INFO[o].word;
            a.iter().zip(b).zip(&masks).map(|((&p, &q), &m)| f(p as u128, q as u128, m) as u8).collect()
        };
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
                            let v = zip(o, va, vb);
                            let h = class_hash(&v, o == LT);
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
                                        new.push((term(), v));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        drop(reps);
        // a sampled pair's representative as the build ends: a displaced one is now a member
        for (u, r) in st.sample.iter_mut() {
            if let Some(&n) = moved.get(r) {
                (*u, *r) = if *u == n { (*r, n) } else { (*u, n) };
            }
        }
        let memos = key.sets.iter().map(|(w, ins)| ValueMemo::new(*w, ins.len(), (0..3).map(|v| ins.iter().map(|x| x[v] as u8).collect()).collect())).collect();
        st.millis = t0.elapsed().as_millis();
        (Classes { map, memos: Mutex::new(memos) }, st)
    }

    /// The process's table, built from `KEY_FILE` on first use; a key learned for another table fails the process.
    pub fn get() -> &'static Classes {
        CLASSES.get_or_init(|| {
            let key = Key::parse(KEY_FILE).unwrap_or_else(|e| panic!("{e}"));
            let (c, st) = Classes::build(&key, SIZE, 0, 0);
            println!("CLASSES {} classes ({} lt) to size {SIZE} under {} key inputs, built in {} ms", c.len(), st.lts, key.len(), st.millis);
            c
        })
    }

    /// Classes in the table.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// The representative of `t`'s class when the table knows it and it is not `t`; `None` otherwise, and for a term over a
    /// variable other than x, y, z. Pure: no proof.
    pub fn rep(&self, t: &Term) -> Option<Term> {
        if t.max_var() >= 3 {
            return None;
        }
        let mut vals = vec![];
        for m in self.memos.lock().unwrap_or_else(|e| e.into_inner()).iter_mut() {
            vals.extend_from_slice(m.values(t));
        }
        let r = *self.map.get(&class_hash(&vals, matches!(*t.node(), Node::Op(LT, ..))))?;
        (r != *t).then_some(r)
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
