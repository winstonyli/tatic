//! Whether `tree_encoding`'s second attempt, over the reachable carry states, can find what the first, over all of them, misses.
//! It should not: Moore classes are a stable partition, so `try_encoding` cannot fail on them, and whether the start states share
//! a class depends only on states they reach. PARKED.md, "Delete the reachability guard": this check goes with that guard.
use crate::machine::*;
use crate::rewrite::*;

const N: usize = 4;
const K: usize = 2;
const MASK: u8 = (1 << N) - 1;

fn value(t: &Term, x: [u8; K]) -> u8 {
    match *t.node() {
        Node::V(i) => x[i],
        Node::Zero => 0,
        Node::Ones => MASK,
        Node::Op(o, a, b) => {
            let (a, b) = (value(&a, x), value(&b, x));
            match o {
                ADD => a.wrapping_add(b) & MASK,
                AND => a & b,
                OR => a | b,
                XOR => a ^ b,
                SUB => a.wrapping_sub(b) & MASK,
                LT => (a < b) as u8,
                SHL1 => (a << 1) & MASK,
                _ => unreachable!("not enumerated"),
            }
        }
    }
}

/// Every term of at most two levels of the machine's operators over two variables and the constants.
fn terms() -> Vec<Term> {
    let leaves = [Term::v(0), Term::v(1), Term::ZERO, Term::ONES];
    let step = |xs: &[Term], ys: &[Term]| {
        let mut out: Vec<Term> = xs.iter().map(|a| Term::op(SHL1, *a, Term::ZERO)).collect();
        for o in [ADD, AND, OR, XOR, SUB, LT] {
            for a in xs {
                for b in ys {
                    out.push(Term::op(o, *a, *b));
                }
            }
        }
        out
    };
    let mut level1 = leaves.to_vec();
    level1.extend(step(&leaves, &leaves));
    let mut all = level1.clone();
    all.extend(step(&level1, &level1));
    all.sort();
    all.dedup();
    all
}

#[test]
fn the_reachable_attempt_never_beats_the_full_one() {
    const PAIRS_PER_CLASS: usize = 400;
    // terms equal at this width, each with its machine and reachable states
    let mut classes: hashbrown::HashMap<Vec<u8>, Vec<(Machine, Vec<bool>)>> = Default::default();
    for t in terms() {
        let Some(m) = Machine::parse(&t) else { continue };
        let table: Vec<u8> = (0..1u16 << (2 * N)).map(|i| value(&t, [i as u8 & MASK, (i >> N) as u8 & MASK])).collect();
        let reach = reachable(&raw_table(&m, K));
        classes.entry(table).or_default().push((m, reach));
    }
    let (mut tried, mut both_found, mut full_only, mut both_missed, mut dropped) = (0usize, 0usize, 0usize, 0usize, 0usize);
    for class in classes.values() {
        let mut in_class = 0;
        for (i, (m1, r1)) in class.iter().enumerate() {
            for (m2, r2) in &class[i + 1..] {
                let unreachable_state = r1.iter().chain(r2).any(|x| !*x);
                if !unreachable_state || m1.last() != m2.last() || m1.carries() + m2.carries() == 0 {
                    continue;
                }
                in_class += 1;
                if in_class > PAIRS_PER_CLASS {
                    dropped += 1;
                    continue;
                }
                tried += 1;
                let reach = [r1.clone(), r2.clone()];
                let (full, restricted) = (moore_encoding(m1, m2, K, None), moore_encoding(m1, m2, K, Some(&reach)));
                assert!(full.is_some() || restricted.is_none(), "the second attempt found what the first missed: {} / {}", m1.key(), m2.key());
                both_found += (full.is_some() && restricted.is_some()) as usize;
                full_only += (full.is_some() && restricted.is_none()) as usize;
                both_missed += full.is_none() as usize;
            }
        }
    }
    eprintln!("reach-ab classes={} tried={tried} both-found={both_found} full-only={full_only} both-missed={both_missed} dropped={dropped}", classes.len());
    // `both_missed` is the pairs where the first attempt failed: the only ones the second could have beaten it on
    assert!(both_found > 100 && both_missed > 100, "the enumeration no longer reaches both outcomes");
}

/// The laws `lt_computes_and_its_laws_are_found_by_the_encoding_search` proves although their carries have unreachable states.
#[test]
fn the_unreachable_state_laws_need_only_the_first_attempt() {
    let op = Term::op;
    let (x, y) = (Term::v(0), Term::v(1));
    for (t1, t2) in [(op(LT, x, Term::ZERO), op(LT, y, Term::ZERO)), (op(LT, op(ADD, x, y), x), op(LT, op(ADD, x, y), y))] {
        let (m1, m2) = (Machine::parse(&t1).unwrap(), Machine::parse(&t2).unwrap());
        let some_unreachable = [&m1, &m2].iter().any(|m| reachable(&raw_table(m, K)).iter().any(|r| !*r));
        assert!(some_unreachable, "{} has no unreachable state", t1.show());
        assert!(moore_encoding(&m1, &m2, K, None).is_some(), "{} = {}", t1.show(), t2.show());
    }
}
