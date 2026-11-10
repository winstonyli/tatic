//! The law supply: operator-set streams of open laws (`stream_laws`), merged round-robin per salt into the memoized
//! sequence the loops and the extras read (`stream_sequence`), and the phase windows over it (`residue`).

use super::rewrite::Node;
use super::search::{leaves3, mk};
use super::*;
use hashbrown::HashSet;

/// The rotation (spec decision 8): every set of two and three of the seven bit-vector operators, none with `lt`.
#[test]
pub fn stream_sets_are_the_pairs_and_triples() {
    let sets = stream_sets();
    assert_eq!(sets.len(), 56);
    assert_eq!(sets.iter().filter(|s| s.len() == 2).count(), 21);
    assert!(sets.iter().all(|s| (2..=3).contains(&s.len()) && !s.contains(&LT)));
}

/// Review Focus 3: a stream is the same laws in the same order on every call (two direct calls, not the memo); another
/// salt gives other laws; every law's sides use only the set's operators, the table leaves it open, and it agrees on
/// the 4096 width-8 inputs.
#[test]
pub fn stream_laws_are_deterministic_and_open() {
    let ops = [ADD, SHR1];
    let (a, b) = (stream_laws(&ops, 1, 2000, 2), stream_laws(&ops, 1, 2000, 2));
    assert!(a.len() > 20, "{} laws", a.len());
    assert!(a == b, "same salt, other laws or order");
    assert!(a != stream_laws(&ops, 2, 2000, 2), "another salt, the same laws");
    fn within(t: &Term, ops: &[usize]) -> bool {
        match *t.node() {
            Node::Op(o, x, y) => ops.contains(&o) && within(&x, ops) && within(&y, ops),
            _ => true,
        }
    }
    let c = crate::classes::Classes::get();
    let job = &mut Job::new(Setup::process());
    let mut r8 = width8();
    tatic_kernel::scoped(|| {
        let memo = &mut crate::classes::NormalForms::default();
        for ((x, y), _) in &a {
            assert!(within(x, &ops) && within(y, &ops), "{} = {}", x.show(), y.show());
            assert!(c.normalize(job, 4, 3, x, memo) != c.normalize(job, 4, 3, y, memo), "closed: {} = {}", x.show(), y.show());
            assert!(r8.agree(x, y), "{} = {}", x.show(), y.show());
        }
    });
}

/// Phases are residue classes at `STREAM_STRIDE`, windowed by skip and count.
#[test]
pub fn residue_takes_a_phase_window() {
    let seq: Vec<(Term, Term)> = (0..40).map(|i| (Term::v(0), (0..i).fold(Term::v(1), |t, _| Term::op(ADD, t, Term::v(2))))).collect();
    let at = |w: Vec<(Term, Term)>| w.iter().map(|l| seq.iter().position(|s| s == l).unwrap()).collect::<Vec<_>>();
    assert_eq!(at(residue(&seq, 1, 0, 3)), [1, 5, 9]);
    assert_eq!(at(residue(&seq, 2, 1, 2)), [6, 10]);
    assert_eq!(at(residue(&seq, 3, 9, 5)), [39]);
}

/// The streams' operator sets (spec decision 8): every set of two and three of the seven bit-vector operators, in the
/// order of their bit masks over `[ADD, AND, OR, XOR, SUB, SHL1, SHR1]` (as `docs/runs/2026-10-23/scripts/mix_streams.sh`).
pub fn stream_sets() -> Vec<Vec<usize>> {
    let ops = [ADD, AND, OR, XOR, SUB, SHL1, SHR1];
    (1u32..128).filter(|m| matches!(m.count_ones(), 2 | 3)).map(|m| (0..7).filter(|i| m >> i & 1 == 1).map(|i| ops[i]).collect()).collect()
}

/// Terms grown per level of a stream (the probe's budget, docs/tier-cycle/ "Triples match pairs per grown term").
pub const STREAM_BUDGET: usize = 20000;

/// The stream laws' variables (`x`, `y`, `z`).
pub const STREAM_VARS: usize = 3;
// `Term::occurrences` counts into `[usize; 8]` (scorer features): a variable index must stay below 8
const _: () = assert!(STREAM_VARS <= 8);
/// Growth levels of a stream.
pub const STREAM_LEVELS: usize = 2;
/// Phases of the stream sequence: a sweep's loops serve 1-3 (spec §9); 0 fed the mines' extras until 2026-10-28 and is
/// left to a single loop's default SPHASE.
pub const STREAM_STRIDE: usize = 4;

/// The 4096 pseudo-random width-8 inputs an open law must agree on (the probe's): width 4 only conjectured it.
fn width8() -> ValueMemo<u8> {
    let mut seed = 0x6a09_e667_f3bc_c908u128;
    let vars: std::sync::Arc<[Box<[u8]>]> = (0..3)
        .map(|_| {
            (0..4096)
                .map(|_| {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    (seed >> 40) as u8
                })
                .collect()
        })
        .collect();
    ValueMemo::new(8, 4096, vars)
}

/// One stream (spec §9; the probe `open_law_counts`, `docs/runs/2026-10-23/patches/open_law_counts_table.patch`): seeds
/// are the class table's representatives whose operators lie in `ops`; `levels` times, one leaf of a term is grown into
/// one of the seeds' operators over two leaves (`shl1` and `shr1` over one), padding dropped, about `budget` terms per
/// level drawn by `salt`. Laws are grouped by width-4 values as `pool_conjectures` does, have a grown side, use all three
/// variables, and are shuffled by `salt`; kept when the table leaves them open (normal forms differ) and they agree on
/// `width8`'s inputs. Each law comes with its depth, the level of its deeper side. Prints the laws kept and refuted.
///
/// The laws of depth at most `d` are the stream grown `d` times, in its order (`at_depth`;
/// `a_deeper_stream_restricted_is_the_shallow_one`): levels up to `d` draw the same terms, a group's head is its least
/// member by level so a deeper member never heads a shallower one, and `shuffled` sorts by a key of the law alone.
pub fn stream_laws(ops: &[usize], salt: usize, budget: usize, levels: usize) -> Vec<((Term, Term), usize)> {
    let c = crate::classes::Classes::get();
    fn within(t: Term, ops: &[usize]) -> bool {
        match *t.node() {
            Node::Op(o, a, b) => ops.contains(&o) && within(a, ops) && within(b, ops),
            _ => true,
        }
    }
    let mut seeds: Vec<Term> = c.reps().filter(|t| within(*t, ops)).collect();
    seeds.sort_unstable();
    fn ops_of(t: Term, out: &mut std::collections::BTreeSet<usize>) {
        if let Node::Op(o, a, b) = *t.node() {
            out.insert(o);
            ops_of(a, out);
            ops_of(b, out);
        }
    }
    // the leaf positions of a term (a shift's second operand is not one), and the term with leaf `k` replaced by `g`
    fn leaf_count(t: Term) -> usize {
        match *t.node() {
            Node::Op(SHL1 | SHR1, a, _) => leaf_count(a),
            Node::Op(_, a, b) => leaf_count(a) + leaf_count(b),
            _ => 1,
        }
    }
    fn replaced(t: Term, k: &mut Option<usize>, g: Term) -> Term {
        match *t.node() {
            Node::Op(o @ (SHL1 | SHR1), a, b) => Term::op(o, replaced(a, k, g), b),
            Node::Op(o, a, b) => {
                let a = replaced(a, k, g);
                Term::op(o, a, replaced(b, k, g))
            }
            _ => match *k {
                Some(0) => {
                    *k = None;
                    g
                }
                Some(i) => {
                    *k = Some(i - 1);
                    t
                }
                None => t,
            },
        }
    }
    let mut grown_ops = std::collections::BTreeSet::new();
    seeds.iter().for_each(|t| ops_of(*t, &mut grown_ops));
    let leaves = &leaves3();
    let mut memo = ValueMemo::exhaustive(4, 3);
    let leaf_classes: Vec<u32> = leaves.iter().map(|l| memo.class(l)).collect();
    let grow: Vec<Term> = grown_ops
        .iter()
        .flat_map(|&o| if o == SHL1 || o == SHR1 { leaves.iter().map(|a| mk(o, a, &Term::ZERO)).collect::<Vec<_>>() } else { leaves.iter().flat_map(|a| leaves.iter().map(move |b| mk(o, a, b))).collect() })
        .filter(|g| !leaf_classes.contains(&memo.class(g)))
        .collect();
    let mut level: hashbrown::HashMap<Term, usize> = seeds.iter().map(|t| (*t, 0)).collect();
    // the pool, in growth order: a term's rank is its level, and a group's head the least by (level, text)
    let mut pool: Vec<(usize, Term)> = seeds.iter().map(|t| (0, *t)).collect();
    let (mut base, mut i) = (seeds.clone(), 0u64);
    for l in 1..=levels {
        let total: usize = base.iter().map(|t| leaf_count(*t)).sum::<usize>() * grow.len();
        let mut next = vec![];
        for t in &base {
            for p in 0..leaf_count(*t) {
                for g in &grow {
                    i += 1;
                    if (tatic_rng::mix64(i ^ tatic_rng::mix64(salt as u64 + 13 * l as u64)) % total.max(1) as u64) < budget as u64 {
                        let w = replaced(*t, &mut Some(p), *g);
                        if !level.contains_key(&w) {
                            level.insert(w, l);
                            next.push(w);
                            pool.push((l, w));
                        }
                    }
                }
            }
        }
        base = next;
    }
    let laws: Vec<(Term, Term)> =
        pool_conjectures(pool, 4, 3).into_iter().filter(|(a, b)| level[a].max(level[b]) > 0 && (0..3).all(|v| a.has_var(v) || b.has_var(v))).collect();
    let job = &mut Job::new(Setup::process());
    let mut r8 = width8();
    let (mut out, mut refuted) = (vec![], 0usize);
    tatic_kernel::scoped(|| {
        let memo = &mut crate::classes::NormalForms::default();
        for (a, b) in shuffled(laws, salt) {
            if c.normalize(job, 4, 3, &a, memo) == c.normalize(job, 4, 3, &b, memo) {
                continue;
            }
            if !r8.agree(&a, &b) {
                refuted += 1;
                continue;
            }
            out.push(((a, b), level[&a].max(level[&b])));
        }
    });
    let names: Vec<&str> = ops.iter().map(|o| OP_INFO[*o].name).collect();
    println!("STREAM {} salt {salt}: {} open laws, {refuted} refuted at width 8", names.join(","), out.len());
    out
}

/// A stream's laws of depth at most `d`, in its order.
pub fn at_depth(laws: &[((Term, Term), usize)], d: usize) -> Vec<(Term, Term)> {
    laws.iter().filter(|(_, l)| *l <= d).map(|(law, _)| *law).collect()
}

/// The law sequence for `salt` with the table's representatives grown `levels` times (spec §9; the loops use
/// `STREAM_LEVELS`): the 56 streams (`stream_sets`, `STREAM_BUDGET`) interleaved round-robin, a law kept at its first
/// appearance. One growth count of `stream_sequences`.
pub fn stream_sequence(salt: usize, levels: usize) -> std::sync::Arc<Vec<(Term, Term)>> {
    stream_sequences(salt, &[levels]).pop().unwrap()
}

/// The sequences for `salt` at each of `levels`, from one build of the streams at the deepest of them that is not built
/// yet: a process that needs several asks for them together, deepest work done once (the shallower are its laws of
/// lower depth, `at_depth`). Each is built once per process, salt and growth count, on `STREAM_THREADS` threads
/// (default 4, so three gate processes fill the 12-core cap; clamped to 1..=12; 4 threads: 5.4 s and 2.8 GB against
/// 15.4 s and 1.4 GB serial, run `2026-10-27-cu18-seqmem-b`).
pub fn stream_sequences(salt: usize, levels: &[usize]) -> Vec<std::sync::Arc<Vec<(Term, Term)>>> {
    static MEMO: crate::task::SharedMemo<(usize, usize), std::sync::Arc<Vec<(Term, Term)>>> = crate::task::SharedMemo::new();
    let threads = Setup::process().or("STREAM_THREADS", 4).clamp(1, 12);
    let deepest = levels.iter().copied().filter(|&l| MEMO.get(&(salt, l)).is_none()).max();
    let streams = std::cell::OnceCell::new();
    levels
        .iter()
        .map(|&l| MEMO.with((salt, l), || std::sync::Arc::new(merge_streams(streams.get_or_init(|| build_streams(salt, STREAM_BUDGET, deepest.unwrap(), threads)), salt, l)), |s| s.clone()))
        .collect()
}

/// The streams on `threads` threads, each taking the next stream when free (their costs differ), in `stream_sets` order.
/// A stream is a pure function of its operators, salt, budget and growth count, so the result is the same at any thread
/// count (`a_stream_sequence_is_the_same_on_any_thread_count`).
fn build_streams(salt: usize, budget: usize, levels: usize, threads: usize) -> Vec<Vec<((Term, Term), usize)>> {
    let t0 = std::time::Instant::now();
    let sets = stream_sets();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let mut streams: Vec<Vec<((Term, Term), usize)>> = vec![vec![]; sets.len()];
    std::thread::scope(|sc| {
        let worker = || {
            let mut built = vec![];
            loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(ops) = sets.get(i) else { break built };
                built.push((i, stream_laws(ops, salt, budget, levels)));
            }
        };
        let handles: Vec<_> = (0..threads.min(sets.len())).map(|_| std::thread::Builder::new().stack_size(tatic_kernel::CHECK_STACK).spawn_scoped(sc, worker).unwrap()).collect();
        for h in handles {
            for (i, s) in h.join().unwrap() {
                streams[i] = s;
            }
        }
    });
    println!("STREAMS salt {salt}, {levels} growths: {} streams in {:.1}s on {threads} threads", streams.len(), t0.elapsed().as_secs_f64());
    streams
}

/// The sequence of `streams`' laws of depth at most `levels`: interleaved round-robin, a law kept at its first appearance.
fn merge_streams(streams: &[Vec<((Term, Term), usize)>], salt: usize, levels: usize) -> Vec<(Term, Term)> {
    let streams: Vec<Vec<(Term, Term)>> = streams.iter().map(|s| at_depth(s, levels)).collect();
    let (mut seen, mut seq) = (HashSet::new(), vec![]);
    for i in 0..streams.iter().map(Vec::len).max().unwrap_or(0) {
        for s in &streams {
            if let Some(l) = s.get(i) {
                if seen.insert(*l) {
                    seq.push(*l);
                }
            }
        }
    }
    println!("STREAMS salt {salt}, {levels} growths: {} laws", seq.len());
    seq
}

/// The streams built on one thread and on four give one sequence (at a smaller budget than the loops'). The four-thread
/// build goes first, so the shared memos it reads (`VERDICTS`, `TREE_ENCS`, the class lookups) start as cold as the
/// process allows, and an order-dependent fill would show.
#[test]
fn a_stream_sequence_is_the_same_on_any_thread_count() {
    let parallel = merge_streams(&build_streams(1, 2000, 2, 4), 1, 2);
    assert!(parallel == merge_streams(&build_streams(1, 2000, 2, 1), 1, 2));
}

/// A stream grown deeper and restricted to depth 2 is the stream grown twice, law for law in order (`stream_laws`' note),
/// at three salts for a pair and a triple; and the merged sequence of the deeper streams at depth 2 is the 2-growth
/// sequence, so `stream_sequences` may derive one from the other.
#[test]
fn a_deeper_stream_restricted_is_the_shallow_one() {
    for salt in [0, 1, crate::classes::HELD_SALT] {
        for ops in [&[ADD, SHR1][..], &[ADD, SUB, SHL1]] {
            let shallow: Vec<(Term, Term)> = stream_laws(ops, salt, 2000, 2).into_iter().map(|(law, _)| law).collect();
            let deep = stream_laws(ops, salt, 2000, 3);
            assert!(deep.len() > shallow.len(), "salt {salt}: the third growth added no law");
            assert!(at_depth(&deep, 2) == shallow, "salt {salt}, {} ops: restricted differs", ops.len());
        }
    }
    assert!(merge_streams(&build_streams(1, 2000, 3, 4), 1, 2) == merge_streams(&build_streams(1, 2000, 2, 4), 1, 2));
}

/// FNV-1a 64 of the laws' text, one `lhs = rhs` line each: what the pinned sequences are pinned by.
fn laws_digest(laws: &[(Term, Term)]) -> u64 {
    use std::fmt::Write;
    Fnv::of(|h| {
        laws.iter().try_for_each(|(a, b)| {
            a.show_into(h)?;
            h.write_str(" = ")?;
            b.show_into(h)?;
            h.write_str("
")
        })
    })
}

/// The sequences at the loops' and the extras' growth counts (`STREAM_LEVELS`, and the deepest held band's) at `salt`,
/// from one build as a sweep's parent asks for them (`stream_sequences`), and checked against the pinned length and
/// digest of their laws' text.
fn assert_sequences_pinned(salt: usize, pinned: [(usize, usize, u64); 2]) {
    let seqs = stream_sequences(salt, &pinned.map(|(levels, ..)| levels));
    let got: Vec<(usize, usize, u64)> = pinned
        .iter()
        .zip(&seqs)
        .map(|(&(levels, ..), seq)| {
            let fnv = laws_digest(seq);
            println!("PINNED salt {salt}, {levels} growths: {} laws, digest {fnv:#018x}", seq.len());
            (levels, seq.len(), fnv)
        })
        .collect();
    assert_eq!(got, pinned, "a sequence changed");
}

/// The two sequences a sweep builds at salt 1 (the loops' at `STREAM_LEVELS` growths, the extras' at the deepest held
/// band's), pinned by length and an FNV-1a digest of their laws' text: a cheaper way to group, order or filter the
/// streams' terms must leave them byte-identical (docs/tier-cycle/, "Grouping the streams' terms, and the 2-growth build
/// inside the 4-growth one"). Its own run is the workload for counting a build's instructions.
#[test]
#[ignore]
pub fn stream_sequences_are_pinned() {
    let deep = crate::classes::held_levels(crate::classes::HELD_BANDS.into_iter().max().unwrap());
    assert_sequences_pinned(1, [(STREAM_LEVELS, 58125, 0x7703_133d_0c24_dbb2), (deep, 230801, 0x4bb4_78c5_da79_675b)]);
}

/// The same two sequences at salt 0, the order a bare `loop_stream` or `rule_miner` run (`RULEMINER_SHUFFLE` unset) gets.
#[test]
#[ignore]
pub fn stream_sequences_are_pinned_at_salt_0() {
    let deep = crate::classes::held_levels(crate::classes::HELD_BANDS.into_iter().max().unwrap());
    assert_sequences_pinned(0, [(STREAM_LEVELS, 58440, 0x4a7d_c226_0672_672b), (deep, 230399, 0x8966_904d_38ac_dd30)]);
}

/// Small streams (a pair, 2000 terms a level over 2 levels; a triple, 4000 over 3) at salts 0, 1 and the held salt, pinned
/// by length and digest: the guard every suite run carries beside the ignored `stream_sequences_are_pinned` and
/// `stream_sequences_are_pinned_at_salt_0`, which pin the loops' scale.
#[test]
pub fn small_streams_are_pinned() {
    const HELD: usize = crate::classes::HELD_SALT;
    const PAIR: (&[usize], usize, usize) = (&[ADD, SHR1], 2000, 2);
    const TRIPLE: (&[usize], usize, usize) = (&[ADD, SUB, SHL1], 4000, 3);
    let pinned: [(usize, (&[usize], usize, usize), usize, u64); 6] = [
        (0, PAIR, 199, 0x1201_43b8_61ec_c526),
        (1, PAIR, 200, 0x9a5d_e4a5_acf0_86c9),
        (HELD, PAIR, 170, 0xc7e5_8bda_80cc_fcb1),
        (0, TRIPLE, 521, 0xe70f_82ea_e9e3_73a5),
        (1, TRIPLE, 442, 0x779f_6033_c943_06fc),
        (HELD, TRIPLE, 468, 0x9304_50b2_3cd1_95f9),
    ];
    let got: Vec<(usize, (&[usize], usize, usize), usize, u64)> = pinned
        .iter()
        .map(|&(salt, (ops, budget, levels), ..)| {
            let laws = at_depth(&stream_laws(ops, salt, budget, levels), levels);
            (salt, (ops, budget, levels), laws.len(), laws_digest(&laws))
        })
        .collect();
    assert_eq!(got, pinned, "a small stream changed");
}

/// Phase `phase`'s window of a sequence: its residue class at `STREAM_STRIDE`, `laws` of them from `skip`.
pub fn residue(seq: &[(Term, Term)], phase: usize, skip: usize, laws: usize) -> Vec<(Term, Term)> {
    seq.iter().skip(phase).step_by(STREAM_STRIDE).skip(skip).take(laws).cloned().collect()
}

/// Builds `stream_sequence(STREAMS_SALT)` (default 1) and prints its size and time: what a sweep pays once for its loops'
/// laws (spec §9, Risks) when it builds no deeper one (`driver::scope_extras` asks for both at once).
#[test]
#[ignore]
pub fn stream_sequence_cost() {
    let salt = Setup::process().or("STREAMS_SALT", 1usize);
    let seq = stream_sequence(salt, STREAM_LEVELS);
    println!("SEQUENCE salt {salt}: {} laws; phase 1 window of 300: {}", seq.len(), residue(&seq, 1, 0, 300).len());
}
