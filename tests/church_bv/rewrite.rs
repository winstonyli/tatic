use super::*;
use std::{cmp::Reverse, collections::BinaryHeap, rc::Rc};

/// A hash-consed term: a pointer to its one node. Leaves are statics, `Op` nodes are interned (`Term::op`) and never
/// freed, so equal terms are the same pointer: `==` and `Hash` take the address, and clone is a copy. Each node also
/// carries what is computed bottom-up once, when it is made: its size, the set of its variables and its shape.
/// `show()` is for text (files, logs, lemma names) and the text orders. `Ord` is structural (`V < Zero < Ones < Op`,
/// then fields), the order the derived one gave; it only makes canonical keys (a sorted rule set).
#[derive(Clone, Copy)]
pub struct Term(&'static Interned);
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Node {
    V(usize),
    Zero,
    Ones,
    Op(usize, Term, Term),
}
struct Interned {
    node: Node,
    size: usize,
    /// Bit `i` set when `V(i)` occurs.
    vars: u64,
    /// See `Term::shape`.
    shape: u64,
    /// See `Term::sh`.
    sh: u64,
}
impl Interned {
    const fn leaf(node: Node, vars: u64, shape: u64, sh: u64) -> Interned {
        Interned { node, size: 1, vars, shape, sh: mix(sh) }
    }
}
/// A 64-bit finaliser (murmur3's), so that every bit of the input reaches every bit of the hash.
const fn mix(mut h: u64) -> u64 {
    h ^= h >> 33;
    h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
    h ^= h >> 33;
    h = h.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    h ^ h >> 33
}
/// `Term::sh` of `Op(o, a, b)` from its children's.
fn sh_op(o: usize, a: u64, b: u64) -> u64 {
    mix(a ^ mix(b.wrapping_add(o as u64)))
}
// Shape bits: 0..8 an operator at the root; 8..61 (operator, side, child `class`), the 176 of them folded into 53 bits;
// 61, 62, 63 a leaf V, Ones, Zero. `RuleTable` keeps exact per-operand class masks instead: it tests one term at a time,
// where the folding would only admit rules that cannot match.
const fn side_bit(o: usize, side: usize, c: usize) -> u64 {
    1 << (8 + ((o * 2 + side) * CLASSES + c) % 53)
}
const V_SHAPE: u64 = 1 << 61;
const ONES_SHAPE: u64 = 1 << 62;
const ZERO_SHAPE: u64 = 1 << 63;
static LEAVES: [Interned; 64] = {
    let mut a = [const { Interned::leaf(Node::Zero, 0, ZERO_SHAPE, 64) }; 64];
    let mut i = 0;
    while i < 64 {
        a[i] = Interned::leaf(Node::V(i), 1 << i, V_SHAPE, i as u64);
        i += 1;
    }
    a
};
// The leaf consts name statics: a promoted `&Interned` need not have one address.
static ZERO_NODE: Interned = Interned::leaf(Node::Zero, 0, ZERO_SHAPE, 64);
static ONES_NODE: Interned = Interned::leaf(Node::Ones, 0, ONES_SHAPE, 65);
const SHARDS: usize = 16;
/// Each thread's last `Term::op` node per slot of the hash, in front of the shared table. Nearly every call finds a node
/// that exists (99% in a cmp3d mine, almost all from the join), and the table's lock and lookup were over half of that
/// mine's time; 2^16 slots (512 KB) took its job CPU from 25.8 to 16.9 s, 2^12 to 2^18 all helped (docs/tier-cycle.md,
/// "The interner's per-thread cache").
const OP_CACHE_SLOTS: usize = 1 << 16;
thread_local! {
    static OP_CACHE: Box<[std::cell::Cell<u64>]> = (0..OP_CACHE_SLOTS).map(|_| std::cell::Cell::new(0)).collect();
}
/// A node's address with a 16-bit `tag` from its hash in the top bits (user addresses are below 2^48), 0 for none: the
/// interner's cache slots and cells hold these, so a lookup passes over another node without loading it (loads of cold
/// nodes were most of `Term::op`'s cost, docs/tier-cycle.md, "Profile after the lock-free reads and the memo per
/// candidate").
fn tagged(m: &'static Interned, tag: u64) -> u64 {
    let p = m as *const Interned as u64;
    assert!(p >> 48 == 0, "a node address past 48 bits");
    p | tag << 48
}
/// The node in `w` when its tag is `tag`.
fn untag(w: u64, tag: u64) -> Option<&'static Interned> {
    // SAFETY: a nonzero word is `tagged` from a leaked `Interned` node, never freed
    (w != 0 && w >> 48 == tag).then(|| unsafe { &*((w & ((1 << 48) - 1)) as *const Interned) })
}
/// One shard's open-addressed cells (linear probing from the hash's low bits), each 0 or a node `tagged` with the hash's
/// top 16 bits. Cells only go from 0 to a node, and a shard's cells are replaced only by a larger copy, so a reader needs
/// no lock: it may miss a node made since it loaded the cells, and then looks again under the shard's lock. Replaced cells
/// are never freed (a reader may still hold them); a table that grows by doubling leaves at most its own size behind.
struct Cells {
    mask: usize,
    cells: Box<[std::sync::atomic::AtomicU64]>,
}
impl Cells {
    fn new(len: usize) -> &'static Cells {
        Box::leak(Box::new(Cells { mask: len - 1, cells: (0..len).map(|_| std::sync::atomic::AtomicU64::new(0)).collect() }))
    }
    /// The node `n` (hash `h`), or the free cell where it would go.
    fn find(&self, h: u64, n: &Node) -> Result<&'static Interned, usize> {
        let mut i = h as usize & self.mask;
        loop {
            let w = self.cells[i].load(std::sync::atomic::Ordering::Acquire);
            if w == 0 {
                return Err(i);
            }
            if let Some(m) = untag(w, h >> 48).filter(|m| m.node == *n) {
                return Ok(m);
            }
            i = (i + 1) & self.mask;
        }
    }
}
const FIRST_CELLS: usize = 1 << 10;
/// Each shard's cells and, behind its lock, its node count; inserts take the lock, lookups do not (`Cells`).
static TABLE: [(std::sync::atomic::AtomicPtr<Cells>, std::sync::Mutex<usize>); SHARDS] =
    [const { (std::sync::atomic::AtomicPtr::new(std::ptr::null_mut()), std::sync::Mutex::new(0)) }; SHARDS];
fn cells(shard: usize) -> Option<&'static Cells> {
    let p = TABLE[shard].0.load(std::sync::atomic::Ordering::Acquire);
    // SAFETY: the pointer is null or a leaked `Cells`, never freed
    (!p.is_null()).then(|| unsafe { &*p })
}
/// The table's hash of `Op(o, a, b)`: unseeded, so every call agrees (a default-built seeded hasher may not).
fn op_hash(o: usize, a: Term, b: Term) -> u64 {
    mix(o as u64 ^ a.addr().rotate_left(21) ^ b.addr().rotate_left(43))
}
impl Term {
    pub const ZERO: Term = Term(&ZERO_NODE);
    pub const ONES: Term = Term(&ONES_NODE);
    pub fn v(i: usize) -> Term {
        assert!(i < LEAVES.len(), "variable {i} past the leaf table");
        Term(&LEAVES[i])
    }
    /// The one node `Op(o, a, b)`, made on first sight. The shard is bits 40..44 of the hash, apart from the low
    /// bits its cells probe from; a lookup takes no lock, and only a new node takes the shard's (`Cells`). The thread's
    /// `OP_CACHE` slot (bits 44..60, its node `tagged` with the low 16) is tried first: nodes are never freed, so a cached
    /// node stays the term's one node.
    pub fn op(o: usize, a: Term, b: Term) -> Term {
        crate::work::count(crate::work::Site::Op);
        let (h, n) = (op_hash(o, a, b), Node::Op(o, a, b));
        OP_CACHE.with(|c| {
            let slot = &c[(h >> 44) as usize % OP_CACHE_SLOTS];
            if let Some(m) = untag(slot.get(), h & 0xffff).filter(|m| m.node == n) {
                return Term(m);
            }
            let shard = (h >> 40) as usize % SHARDS;
            let m = match cells(shard).map(|c| c.find(h, &n)) {
                Some(Ok(m)) => m,
                _ => Term::insert(shard, h, n),
            };
            slot.set(tagged(m, h & 0xffff));
            Term(m)
        })
    }
    /// `n`'s node, made under the shard's lock unless another thread made it first; the cells double past 3/4 full.
    fn insert(shard: usize, h: u64, n: Node) -> &'static Interned {
        use std::sync::atomic::Ordering;
        let mut count = TABLE[shard].1.lock().unwrap();
        let mut c = cells(shard).unwrap_or_else(|| {
            let c = Cells::new(FIRST_CELLS);
            TABLE[shard].0.store(c as *const Cells as *mut Cells, Ordering::Release);
            c
        });
        let free = match c.find(h, &n) {
            Ok(m) => return m,
            Err(i) => i,
        };
        let Node::Op(o, a, b) = n else { unreachable!("only Op nodes are interned") };
        let shape = 1 << o | side_bit(o, 0, class(&a)) | side_bit(o, 1, class(&b));
        let m: &'static Interned = Box::leak(Box::new(Interned { node: n, size: 1 + a.0.size + b.0.size, vars: a.0.vars | b.0.vars, shape, sh: sh_op(o, a.0.sh, b.0.sh) }));
        let at = if (*count + 1) * 4 > c.cells.len() * 3 {
            let grown = Cells::new(c.cells.len() * 2);
            for w in c.cells.iter().map(|w| w.load(Ordering::Relaxed)) {
                let Some(Node::Op(o, a, b)) = untag(w, w >> 48).map(|m| m.node) else { continue };
                let Err(i) = grown.find(op_hash(o, a, b), &Node::Zero) else { unreachable!("a node is in its cells once") };
                grown.cells[i].store(w, Ordering::Relaxed);
            }
            TABLE[shard].0.store(grown as *const Cells as *mut Cells, Ordering::Release);
            c = grown;
            let Err(i) = c.find(h, &n) else { unreachable!("a new node") };
            i
        } else {
            free
        };
        c.cells[at].store(tagged(m, h >> 48), Ordering::Release);
        *count += 1;
        m
    }
    pub fn node(&self) -> &'static Node {
        &self.0.node
    }
    fn addr(self) -> u64 {
        self.0 as *const Interned as u64
    }
    /// Number of nodes.
    pub fn size(&self) -> usize {
        self.0.size
    }
    /// Whether variable `v` occurs in the term (`show().contains(..)` would also match `xor` and `sub`).
    pub fn has_var(&self, v: usize) -> bool {
        v < 64 && self.0.vars >> v & 1 == 1
    }
    /// The largest variable index, 0 when there is none.
    pub fn max_var(&self) -> usize {
        63usize.saturating_sub(self.0.vars.leading_zeros() as usize)
    }
    /// The root's operator and the classes of its two children (or the leaf's class), as bits. `match_pat(p, t)` compares
    /// node kinds before it recurses, so it holds only where `t.shape()` has every bit of `p.needs()`.
    pub fn shape(&self) -> u64 {
        self.0.shape
    }
    /// A hash of the term's structure (`sh_op` of its children's, from the leaves up), which `subst_sig` computes for a term
    /// not yet made: `join_search` finds a step's term among those reached without making it.
    fn sh(&self) -> u64 {
        self.0.sh
    }
    /// The shape bits a term must have for this pattern to match it: none for a variable, and none for a variable child.
    pub fn needs(&self) -> u64 {
        match *self.node() {
            Node::V(_) => 0,
            Node::Op(o, a, b) => {
                let child = |side, x: Term| if matches!(*x.node(), Node::V(_)) { 0 } else { side_bit(o, side, class(&x)) };
                1 << o | child(0, a) | child(1, b)
            }
            _ => self.shape(),
        }
    }
}
impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}
impl Eq for Term {}

/// `Term::op` makes one node per term whatever a thread's cache holds: terms made on another thread are the same pointers,
/// and each node is the one asked for, with more terms than cache slots so that slots are shared.
#[test]
fn op_is_one_node_per_term_across_threads() {
    let build = || {
        let mut level = vec![Term::v(0), Term::v(1), Term::ZERO, Term::ONES];
        let mut out = vec![];
        for _ in 0..3 {
            let mut next = vec![];
            for o in 0..5 {
                for &a in &level {
                    for &b in level.iter().take(100_000 / (5 * level.len()) + 1) {
                        next.push(((o, a, b), Term::op(o, a, b)));
                    }
                }
            }
            level = next.iter().map(|e| e.1).collect();
            out.extend(next);
        }
        out
    };
    let (here, there, again) = (build(), std::thread::spawn(build).join().unwrap(), build());
    assert!(here.len() > 1 << 16, "more terms than cache slots");
    for (((o, a, b), t), (_, u)) in here.iter().zip(&there) {
        assert!(*t.node() == Node::Op(*o, *a, *b), "the node asked for");
        assert!(t == u, "one node across threads");
    }
    assert!(here.iter().zip(&again).all(|(x, y)| x.1 == y.1), "one node on a second look");
}

/// Threads making the same new terms at once (racing to insert them, and the table growing under them) get one node each.
#[test]
fn op_racing_threads_make_one_node_per_term() {
    let barrier = std::sync::Barrier::new(8);
    let build = || {
        barrier.wait();
        // terms no other test makes: variable 40 on the left of every one
        let mut level = vec![Term::v(40), Term::v(41), Term::v(42)];
        let mut out = vec![];
        for _ in 0..3 {
            let next: Vec<Term> = (0..5).flat_map(|o| level.iter().flat_map(move |&a| [Term::v(40), Term::v(43)].map(|b| (o, a, b)))).map(|(o, a, b)| Term::op(o, a, b)).collect();
            out.extend(&next);
            level = next;
        }
        let wide: Vec<Term> = out.iter().flat_map(|&a| out.iter().take(200).map(move |&b| Term::op(4, a, b))).collect();
        out.extend(wide);
        out
    };
    let all: Vec<Vec<Term>> = std::thread::scope(|s| (0..8).map(|_| s.spawn(build)).collect::<Vec<_>>().into_iter().map(|h| h.join().unwrap()).collect());
    assert!(all[0].len() > 100_000, "enough new terms to grow the table");
    assert!(all.iter().all(|v| v == &all[0]), "one node per term across racing threads");
}

impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.addr().hash(h)
    }
}
impl Ord for Term {
    fn cmp(&self, other: &Term) -> std::cmp::Ordering {
        if self == other {
            return std::cmp::Ordering::Equal;
        }
        let rank = |n: &Node| match n {
            Node::V(_) => 0,
            Node::Zero => 1,
            Node::Ones => 2,
            Node::Op(..) => 3,
        };
        match (*self.node(), *other.node()) {
            (Node::V(i), Node::V(j)) => i.cmp(&j),
            (Node::Op(o, a, b), Node::Op(p, c, d)) => o.cmp(&p).then_with(|| a.cmp(&c)).then_with(|| b.cmp(&d)),
            (x, y) => rank(&x).cmp(&rank(&y)),
        }
    }
}
impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Term) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
/// `Node::Op` indices (the position in `OP_INFO`).
pub const ADD: usize = 0;
pub const AND: usize = 1;
pub const OR: usize = 2;
pub const XOR: usize = 3;
pub const SUB: usize = 4;
pub const LT: usize = 5;
pub const SHL1: usize = 6;
pub const SHR1: usize = 7;
/// `lt` (index 5) returns a one-bit vector and only appears at the root of a term; `shl1` (index 6) is `a << 1`
/// and ignores its second operand (a delay cell in the machine); `shr1` (index 7) is `a >> 1`, also unary, and not a machine.
pub struct OpInfo {
    pub name: &'static str,
    /// a carry (or delay) cell in the machine: add, sub, lt, shl1
    pub carries: bool,
    /// combines its operands' bits at the same position
    pub bitwise: bool,
    pub shift: bool,
    /// head precedence for the rule order's tie-break (higher is greater)
    pub prec: i32,
    /// the operator on single bits (bitwise ops only)
    pub truth: fn(bool, bool) -> bool,
    /// the operator on `n`-bit words, `mask` = 2^n - 1
    pub word: fn(u128, u128, u128) -> u128,
}
const fn info(
    name: &'static str,
    carries: bool,
    bitwise: bool,
    shift: bool,
    prec: i32,
    truth: fn(bool, bool) -> bool,
    word: fn(u128, u128, u128) -> u128,
) -> OpInfo {
    OpInfo { name, carries, bitwise, shift, prec, truth, word }
}
/// Every fact about an operator, indexed as `Node::Op` (the one place that says which ops carry, are bitwise or shift).
fn no_truth(_: bool, _: bool) -> bool {
    panic!("not a bitwise operator")
}
pub const OP_INFO: [OpInfo; 8] = [
    info("add", true, false, false, 6, no_truth, |x, y, m| x.wrapping_add(y) & m),
    info("and", false, true, false, 3, |a, b| a && b, |x, y, _| x & y),
    info("or", false, true, false, 2, |a, b| a || b, |x, y, _| x | y),
    info("xor", false, true, false, 4, |a, b| a != b, |x, y, _| x ^ y),
    info("sub", true, false, false, 5, no_truth, |x, y, m| x.wrapping_sub(y) & m),
    info("lt", true, false, false, 1, no_truth, |x, y, _| (x < y) as u128),
    info("shl1", true, false, true, 0, no_truth, |x, _, m| (x << 1) & m),
    info("shr1", false, false, true, 0, no_truth, |x, _, _| x >> 1),
];
/// `\a _. a << 1`, the Church operator of `Term` index 6.
pub fn shl1_op(n: usize) -> Expr {
    lam(bv_ty(n), lam(bv_ty(n), app(shift_bv(n, 1, true), var(1))))
}
/// `\a _. a >> 1`, the Church operator of `Term` index 7.
pub fn shr1_op(n: usize) -> Expr {
    lam(bv_ty(n), lam(bv_ty(n), app(shift_bv(n, 1, false), var(1))))
}
/// `(proof, type)` of `Pi x y. GoodBv x -> GoodBv y -> GoodBv (shr1 x y)`: output bit `i` is input bit `i + 1`, the top bit false.
pub fn good_shr1(n: usize) -> (Expr, Expr) {
    good_vec(n, shr1_op(n), &move |a, _b, ga, _gb| {
        let s = (0..n).map(|i| if i + 1 < n { a[i + 1] } else { f() }).collect();
        let gs = (0..n).map(|i| if i + 1 < n { ga[i + 1] } else { good_bit(false) }).collect();
        (s, gs)
    })
}
/// `(proof, type)` of `Pi x y. GoodBv x -> GoodBv y -> GoodBv (shl1 x y)`: output bit `i` is input bit `i - 1`, bit 0 false.
pub fn good_shl1(n: usize) -> (Expr, Expr) {
    good_vec(n, shl1_op(n), &move |a, _b, ga, _gb| {
        let s = (0..n).map(|i| if i == 0 { f() } else { a[i - 1] }).collect();
        let gs = (0..n).map(|i| if i == 0 { good_bit(false) } else { ga[i - 1] }).collect();
        (s, gs)
    })
}
/// The Church operators, indexed as `Node::Op`.
pub fn ops_for(n: usize) -> [Expr; 8] {
    [add(n), bitwise(n, &|a, b| and(a, b)), bitwise(n, &|a, b| or(a, b)), bitwise(n, &|a, b| xor(a, b)), sub(n), lt_u(n), shl1_op(n), shr1_op(n)]
}
pub const VARS: [&str; 8] = ["x", "y", "z", "u", "v", "w", "p", "q"];
impl Term {
    pub fn show(&self) -> String {
        let mut s = String::new();
        self.show_into(&mut s);
        s
    }
    fn show_into(&self, out: &mut String) {
        match *self.node() {
            Node::V(i) => out.push_str(VARS[i]),
            Node::Zero => out.push('0'),
            Node::Ones => out.push_str("-1"),
            Node::Op(o, a, b) => {
                out.push_str(OP_INFO[o].name);
                out.push('(');
                a.show_into(out);
                out.push_str(", ");
                b.show_into(out);
                out.push(')');
            }
        }
    }
    /// `self.show().cmp(&other.show())` without allocating (two reused buffers): the text order the rewriter sorts operands by.
    pub fn show_cmp(&self, other: &Term) -> std::cmp::Ordering {
        thread_local! {
            static BUFS: std::cell::RefCell<(String, String)> = Default::default();
        }
        BUFS.with(|b| {
            let (x, y) = &mut *b.borrow_mut();
            x.clear();
            y.clear();
            self.show_into(x);
            other.show_into(y);
            x.as_str().cmp(y.as_str())
        })
    }
    /// The term as an expression, with `vals[i]` for variable `i`.
    pub fn eval(&self, ops: &[Expr], n: usize, vals: &[Expr]) -> Expr {
        match *self.node() {
            Node::V(i) => vals[i],
            Node::Zero => lit(n, 0),
            Node::Ones => lit(n, low_bits(n)),
            Node::Op(o, a, b) => app2(ops[o], a.eval(ops, n, vals), b.eval(ops, n, vals)),
        }
    }
    /// The value on the width-`n` operands `vals`, in plain integers (a cheap screen for false laws).
    pub fn interp(&self, n: usize, vals: &[u128]) -> u128 {
        let mut nodes = 0;
        let v = self.interp_in(low_bits(n), vals, &mut nodes);
        crate::work::count_n(crate::work::Site::Interp, nodes);
        v
    }
    /// `interp` under `mask`, adding the nodes it evaluates to `nodes`.
    fn interp_in(&self, mask: u128, vals: &[u128], nodes: &mut u64) -> u128 {
        *nodes += 1;
        match *self.node() {
            Node::V(i) => vals[i],
            Node::Zero => 0,
            Node::Ones => mask,
            Node::Op(o, a, b) => {
                let (x, y) = (a.interp_in(mask, vals, nodes), b.interp_in(mask, vals, nodes));
                (OP_INFO[o].word)(x, y, mask)
            }
        }
    }
    /// Agrees on random inputs at every width 1..=6 (the plausibility screen every law passes before a machine tries it).
    pub fn is_law(&self, other: &Term, k: usize) -> bool {
        (1..=6).all(|w| self.plausibly_equals(other, w, k))
    }
    /// The smallest width in 1..=6 and an input tuple (over `k` variables) where the two sides differ, if the screen finds one.
    pub fn refute(&self, other: &Term, k: usize) -> Option<(usize, Vec<u128>)> {
        (1..=6).find_map(|w| self.counterexample(other, w, k).map(|vals| (w, vals)))
    }
    /// The first of the corners and 202 pseudo-random width-`n` tuples over `k` variables on which the two sides differ.
    pub fn counterexample(&self, other: &Term, n: usize, k: usize) -> Option<Vec<u128>> {
        self.counterexample_in(other, n, k, SCREEN_INPUTS)
    }
    /// `counterexample` over the first `tries` tuples only (values memoized per term, `ValueMemo`).
    pub fn counterexample_in(&self, other: &Term, n: usize, k: usize, tries: usize) -> Option<Vec<u128>> {
        with_screen(n, k, |m| m.first_difference(self, other, tries).map(|i| m.input(i)))
    }
    /// Whether the two sides differ on one of the first `tries` tuples (`counterexample_in` without building the tuple).
    pub fn differs_in(&self, other: &Term, n: usize, k: usize, tries: usize) -> bool {
        with_screen(n, k, |m| m.first_difference(self, other, tries).is_some())
    }
    /// Whether `self` and `other` agree on the corners and 202 pseudo-random width-`n` tuples over `k` variables.
    pub fn plausibly_equals(&self, other: &Term, n: usize, k: usize) -> bool {
        !self.differs_in(other, n, k, SCREEN_INPUTS)
    }
    pub fn has_shift(&self) -> bool {
        match *self.node() {
            Node::Op(o, a, b) => OP_INFO[o].shift || a.has_shift() || b.has_shift(),
            _ => false,
        }
    }
    /// No add, sub or lt anywhere: bitwise operators and shifts only.
    pub fn add_free(&self) -> bool {
        match *self.node() {
            Node::Op(o, a, b) => (OP_INFO[o].bitwise || OP_INFO[o].shift) && a.add_free() && b.add_free(),
            _ => true,
        }
    }
    pub fn uses_add(&self) -> bool {
        match *self.node() {
            Node::Op(o, a, b) => o == ADD || o == SUB || a.uses_add() || b.uses_add(),
            _ => false,
        }
    }
    /// The term's value at one bit position, a `Bool0`, given the variables' bits (`bits[v]`); bitwise ops only.
    pub fn bit(&self, bits: &[Expr]) -> Expr {
        match *self.node() {
            Node::V(i) => bits[i],
            Node::Zero => f(),
            Node::Ones => t(),
            Node::Op(o, a, b) => {
                let (x, y) = (a.bit(bits), b.bit(bits));
                match o {
                    1 => and(x, y),
                    2 => or(x, y),
                    3 => xor(x, y),
                    _ => panic!("`add` is not bitwise"),
                }
            }
        }
    }
}

/// How `ValueMemo` stores a value: one byte for exhaustive signatures (width at most 8), `u128` for the screen.
pub trait Word: Copy {
    fn of(x: u128) -> Self;
    fn get(self) -> u128;
}

impl Word for u8 {
    fn of(x: u128) -> u8 {
        x as u8
    }
    fn get(self) -> u128 {
        self as u128
    }
}

impl Word for u128 {
    fn of(x: u128) -> u128 {
        x
    }
    fn get(self) -> u128 {
        self
    }
}

/// Terms' width-`n` values on a fixed list of inputs, one vector per interned term, each made from its children's vectors:
/// pools and repeated screens share subterms, so each distinct term is evaluated once per input list. The vectors sit end
/// to end in fixed blocks of about 64 KB (never grown or copied), so a new term rarely allocates and a known one costs a
/// single lookup. One doubling `Vec` was a little slower and held up to 1.4x the memory (docs/tier-cycle.md, "`ValueMemo` in fixed
/// 64 KB blocks").
pub struct ValueMemo<W: Word> {
    mask: u128,
    len: usize,
    /// `vars[v][i]`: variable `v` on input `i`.
    vars: Vec<Box<[W]>>,
    /// Each term's vector's id: vector `id` is the `id % per`-th of block `id / per`.
    ids: hashbrown::HashMap<Term, usize>,
    /// Vectors per block.
    per: usize,
    blocks: Vec<Vec<W>>,
}

/// `out[i] = op(x[i], y[i])` for operator `O`: its `word` is a constant here, so it inlines into the loop (called through
/// the pointer per element it was about 4% of a sweep, docs/tier-cycle.md, "Profile at a7b0719").
fn zip_word<W: Word, const O: usize>(out: &mut [W], x: &[W], y: &[W], mask: u128) {
    let word = const { OP_INFO[O].word };
    for ((o, x), y) in out.iter_mut().zip(x).zip(y) {
        *o = W::of(word(x.get(), y.get(), mask));
    }
}

/// `out[i] = op(x[i], y[i])` for operator `o` at one width's `mask`: `zip_word` picked once per call.
pub fn zip_op<W: Word>(o: usize, out: &mut [W], x: &[W], y: &[W], mask: u128) {
    let zips: [fn(&mut [W], &[W], &[W], u128); OP_INFO.len()] =
        [zip_word::<W, 0>, zip_word::<W, 1>, zip_word::<W, 2>, zip_word::<W, 3>, zip_word::<W, 4>, zip_word::<W, 5>, zip_word::<W, 6>, zip_word::<W, 7>];
    zips[o](out, x, y, mask);
}

/// A `ValueMemo` block's size in bytes (one vector when a vector is larger).
const VALUE_BLOCK: usize = 1 << 16;

/// The screen's input count: all zeros, all ones, then 202 pseudo-random tuples.
const SCREEN_INPUTS: usize = 204;

/// The plausibility screen's value memos, by width and variable count, shared by a process's threads behind one lock: per
/// thread, 66% of a sweep's screen fills redid another thread's (docs/tier-cycle.md, "Per-thread refills"). Pure: values on
/// fixed pseudo-random inputs.
static SCREENS: crate::task::SharedMemo<(usize, usize), ValueMemo<u128>> = crate::task::SharedMemo::new();

/// `f` on the screen's value memo for width `n` and `k` variables.
fn with_screen<R>(n: usize, k: usize, f: impl FnOnce(&mut ValueMemo<u128>) -> R) -> R {
    SCREENS.with((n, k), || ValueMemo::screen(n, k), f)
}

impl<W: Word> ValueMemo<W> {
    pub fn new(n: usize, len: usize, vars: Vec<Box<[W]>>) -> Self {
        let per = (VALUE_BLOCK / (len * std::mem::size_of::<W>())).max(1);
        ValueMemo { mask: low_bits(n), len, vars, ids: Default::default(), per, blocks: vec![] }
    }

    /// `t`'s values, one per input.
    pub fn values(&mut self, t: &Term) -> &[W] {
        let id = self.fill(*t);
        self.vector(id)
    }

    fn vector(&self, id: usize) -> &[W] {
        &self.blocks[id / self.per][id % self.per * self.len..][..self.len]
    }

    /// `t`'s vector's id, made (with its children's) when new.
    fn fill(&mut self, t: Term) -> usize {
        if let Some(&id) = self.ids.get(&t) {
            return id;
        }
        let (len, per) = (self.len, self.per);
        let children = match *t.node() {
            Node::Op(_, a, b) => Some((self.fill(a), self.fill(b))),
            _ => None,
        };
        if self.blocks.last().is_none_or(|b| b.len() == per * len) {
            self.blocks.push(Vec::with_capacity(per * len));
        }
        let id = (self.blocks.len() - 1) * per + self.blocks[self.blocks.len() - 1].len() / len;
        let last = self.blocks.len() - 1;
        match *t.node() {
            Node::V(v) => self.blocks[last].extend_from_slice(&self.vars[v]),
            Node::Zero => self.blocks[last].extend(std::iter::repeat_n(W::of(0), len)),
            Node::Ones => self.blocks[last].extend(std::iter::repeat_n(W::of(self.mask), len)),
            Node::Op(o, ..) => {
                let (a, b) = children.unwrap();
                let mask = self.mask;
                let off = self.blocks[last].len();
                self.blocks[last].resize(off + len, W::of(0));
                // the children's vectors sit in earlier blocks or earlier in the last one
                let (done, tail) = self.blocks.split_at_mut(last);
                let (before, out) = tail[0].split_at_mut(off);
                let at = |id: usize| -> &[W] {
                    let block: &[W] = if id / per == last { before } else { &done[id / per] };
                    &block[id % per * len..][..len]
                };
                zip_op(o, out, at(a), at(b), mask);
            }
        }
        self.ids.insert(t, id);
        id
    }

    /// The first of the first `tries` inputs on which `a` and `b` differ.
    pub fn first_difference(&mut self, a: &Term, b: &Term, tries: usize) -> Option<usize> {
        assert!(tries <= self.len, "{tries} tries over {} inputs", self.len);
        let (a, b) = (self.fill(*a), self.fill(*b));
        let (x, y) = (self.vector(a), self.vector(b));
        (0..tries).find(|&i| x[i].get() != y[i].get())
    }

    /// Input `i`, one value per variable.
    pub fn input(&self, i: usize) -> Vec<u128> {
        self.vars.iter().map(|c| c[i].get()).collect()
    }
}

impl ValueMemo<u8> {
    /// Every width-`n` input over `nv` variables (variable `v` is bits `n*v..` of the input's index), one byte per value.
    pub fn exhaustive(n: usize, nv: usize) -> Self {
        assert!(n <= 8, "exhaustive values hold one byte per input");
        let len = 1usize << (n * nv);
        let vars = (0..nv).map(|v| (0..len).map(|i| (i >> (n * v) & low_bits(n) as usize) as u8).collect()).collect();
        ValueMemo::new(n, len, vars)
    }
}

impl ValueMemo<u128> {
    /// The screen's inputs over `k` variables: all zeros, all ones, then pseudo-random width-`n` tuples.
    fn screen(n: usize, k: usize) -> Self {
        let mask = low_bits(n);
        let mut seed = 0x9e37_79b9_7f4a_7c15u128;
        let mut vars = vec![vec![0u128; SCREEN_INPUTS]; k];
        for i in 0..SCREEN_INPUTS {
            for col in vars.iter_mut() {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                col[i] = match i {
                    0 => 0,
                    1 => mask,
                    _ => (seed >> 40) & mask,
                };
            }
        }
        ValueMemo::new(n, SCREEN_INPUTS, vars.into_iter().map(Vec::into_boxed_slice).collect())
    }
}

/// Leaves, every operator applied to two leaves, and (with `deep`) every operator applied to such a term
/// and a leaf, in either order. Built once per thread for each argument pair and operator count.
pub fn terms(setup: &Setup, nvars: usize, deep: bool) -> std::rc::Rc<[Term]> {
    thread_local! {
        static TERMS: std::cell::RefCell<hashbrown::HashMap<(usize, bool, usize), std::rc::Rc<[Term]>>> = Default::default();
    }
    TERMS.with(|c| c.borrow_mut().entry((nvars, deep, setup.nops())).or_insert_with(|| build_terms(setup, nvars, deep).into()).clone())
}

fn build_terms(setup: &Setup, nvars: usize, deep: bool) -> Vec<Term> {
    let mut leaves: Vec<Term> = (0..nvars).map(Term::v).collect();
    leaves.push(Term::ZERO);
    leaves.push(Term::ONES);
    let mut level1 = vec![];
    for o in 0..setup.nops() {
        for a in &leaves {
            for b in &leaves {
                level1.push(Term::op(o, *a, *b));
            }
        }
    }
    let mut all = leaves.clone();
    all.extend(level1.clone());
    if deep {
        for o in 0..setup.nops() {
            for a in &level1 {
                for b in &leaves {
                    all.push(Term::op(o, *a, *b));
                    all.push(Term::op(o, *b, *a));
                }
            }
        }
    }
    all
}


/// Generic proof of `t1(x, y) = t2(x, y)` for bitwise terms over two good vectors, with no lemma-specific
/// template: per bit, case analysis on the two `GoodBool` witnesses with `refl` leaves (the kernel decides
/// each leaf), then `cong_n` and the two witness eliminations. A false conjecture fails to check.
pub fn bitwise_law(n: usize, t1: &Term, t2: &Term) -> (Expr, Expr) {
    bitwise_law_k(n, 2, t1, t2)
}

/// As `bitwise_law`, over `k` good vectors (terms may use variables `0..k`).
pub fn bitwise_law_k(n: usize, k: usize, t1: &Term, t2: &Term) -> (Expr, Expr) {
    if t1.has_shift() || t2.has_shift() {
        return pos_law(n, k, t1, t2);
    }
    let (bit_law, _) = lemma_n(
        k,
        &|v| id(bool0(), t1.bit(v), t2.bit(v)),
        &|bits| refl(t1.bit(&bits.iter().map(|b| bit(*b)).collect::<Vec<_>>())),
    );
    k_var_law(n, k, t1, t2, &|bits, goods| {
        let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
        for i in 0..n {
            let vs: Vec<Expr> = (0..k).map(|v| bits(v, i)).collect();
            s1.push(t1.bit(&vs));
            s2.push(t2.bit(&vs));
            e.push(apps(bit_law, vs.iter().cloned().chain((0..k).map(|v| goods(v, i))).collect()));
        }
        (s1, s2, e)
    })
}

pub type BitFn<'a> = &'a dyn Fn(usize) -> Expr;
pub type VarBitFn<'a> = &'a dyn Fn(usize, usize) -> Expr;
/// The skeleton of two-variable laws: see `k_var_law`; `per_bit(a, ga, b, gb)` gets the bit and witness variables.
pub fn two_var_law(n: usize, t1: &Term, t2: &Term, per_bit: &dyn Fn(BitFn, BitFn, BitFn, BitFn) -> BitTriple) -> (Expr, Expr) {
    k_var_law(n, 2, t1, t2, &|bits, goods| per_bit(&|i| bits(0, i), &|i| goods(0, i), &|i| bits(1, i), &|i| goods(1, i)))
}

/// The skeleton shared by laws `t1 = t2` over `k` vectors with `GoodBv` witnesses: eliminates the `k` witnesses
/// in turn and calls `per_bit(bits, goods)` (`bits(v, i)`, `goods(v, i)`: bit `i` of vector `v` and its `GoodBool`
/// witness, as variables) for the per-bit equalities `(s1, s2, proofs)`; the result is `Pi x_1..x_k.
/// GoodBv x_1 -> .. -> GoodBv x_k -> Id(Bv_n, t1, t2)`.
pub fn k_var_law(n: usize, k: usize, t1: &Term, t2: &Term, per_bit: &dyn Fn(VarBitFn, VarBitFn) -> BitTriple) -> (Expr, Expr) {
    k_var_law_to(n, k, &bv_ty(n), &|args| (t1.eval(&ops_for(n), n, args), t2.eval(&ops_for(n), n, args)), &|bits, goods| {
        let (s1, s2, e) = per_bit(bits, goods);
        let fbody = bits_to_bv(n);
        cong_n(&bool0(), &bv_ty(n), &fbody, &s1, &s2, e)
    })
}

/// As `k_var_law` for a claim `Id(ty, l, r)` with `(l, r) = sides(vectors)` (`ty` is `Bv_n`, or `Bv_1` for a root
/// `lt`): `finish(bits, goods)` proves it for the bit variables (the vectors are rebuilt by the witness eliminations).
pub fn k_var_law_to(n: usize, k: usize, ty: &Expr, sides: &dyn Fn(&[Expr]) -> (Expr, Expr), finish: &dyn Fn(VarBitFn, VarBitFn) -> Expr) -> (Expr, Expr) {
    // ctx: x_0..x_(k-1), g_0..g_(k-1), then level j adds a_j.. (n bits) and their witnesses (n)
    let level = |j: usize| 2 * k + 2 * n * j;
    let depth = |j: usize| 2 * k + 2 * n * (j + 1);
    let at = |d: usize, pos: usize| var((d - 1 - pos) as u32);
    let last = depth(k - 1);
    let done = finish(&|v, i| at(last, level(v) + i), &|v, i| at(last, level(v) + n + i));
    let claim = |args: Vec<Expr>| {
        let (l, r) = sides(&args);
        id(*ty, l, r)
    };
    // the motive for eliminating vector `j` at depth `d` (inside the previous level's binders), under its own binder
    let motive = |j: usize, d: usize| {
        let args = (0..k)
            .map(|v| {
                if v < j {
                    church_tuple(&(0..n).map(|i| shift(&at(d, level(v) + i), 0, 1)).collect::<Vec<_>>())
                } else if v == j {
                    var(0)
                } else {
                    shift(&at(d, v), 0, 1)
                }
            })
            .collect();
        lam(bv_ty(n), claim(args))
    };
    let mut step = binders(n, done);
    for j in (0..k - 1).rev() {
        step = binders(n, app2(at(depth(j), k + j + 1), motive(j + 1, depth(j)), step));
    }
    let body = app2(at(2 * k, k), motive(0, 2 * k), step);
    let g = || app(good_bv(n), var((k - 1) as u32));
    let mut proof = body;
    let mut stmt = claim((0..k).map(|v| var((2 * k - 1 - v) as u32)).collect());
    for _ in 0..k {
        proof = lam(g(), proof);
        stmt = pi(g(), stmt);
    }
    for _ in 0..k {
        proof = lam(bv_ty(n), proof);
        stmt = pi(bv_ty(n), stmt);
    }
    (proof, stmt)
}

#[test]
pub fn bitwise_law_proves_true_laws_and_rejects_false_ones() {
    let v = |i: usize| Term::v(i);
    let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
    for n in [1usize, 2, 4] {
        for (name, t1, t2) in [
            ("and x y = and y x", op(1, v(0), v(1)), op(1, v(1), v(0))),
            ("xor x x = 0", op(3, v(0), v(0)), Term::ZERO),
            ("or x -1 = -1", op(2, v(0), Term::ONES), Term::ONES),
            ("and x (or x y) = x", op(1, v(0), op(2, v(0), v(1))), v(0)),
        ] {
            let (p, s) = bitwise_law(n, &t1, &t2);
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        for (name, t1, t2) in [("and x y = or x y", op(1, v(0), v(1)), op(2, v(0), v(1))), ("xor x x = -1", op(3, v(0), v(0)), Term::ONES)] {
            let (p, s) = bitwise_law(n, &t1, &t2);
            assert!(holds(&p, &s).is_err(), "false law `{name}` must be rejected at n={n}");
        }
    }
}

// ---- Rewriting with proven lemmas (search note section 10). An `add` conjecture is simplified on both sides by
// the library lemmas `add a 0 = a`, `add 0 a = a` and `add a b = add b a` (the last used to order the operands),
// each rewrite justified by `cong_n` on the enclosing operator and chained with `trans_proof`; if the two
// results are then equal, or both add-free, `bitwise_law` closes the gap.

thread_local! {
    pub static CLOSED: std::cell::RefCell<hashbrown::HashMap<String, (tatic::kernel::PExpr, tatic::kernel::PExpr)>> = Default::default();
}
/// A closed library term built once per key (the proofs and witnesses the rewriter reuses at every step).
pub fn memo(key: String, build: impl FnOnce() -> (Expr, Expr)) -> (Expr, Expr) {
    if let Some(v) = CLOSED.with(|c| c.borrow().get(&key).map(|(p, s)| (p.get(), s.get()))) {
        return v;
    }
    let (p, s) = build();
    CLOSED.with(|c| c.borrow_mut().insert(key, (tatic::kernel::persist(p), tatic::kernel::persist(s))));
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
    scopes.push((sc, p.map(tatic::kernel::persist)));
    job.lemmas.bound.insert(key, (tatic::kernel::persist(r), tatic::kernel::persist(s)));
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
    /// none (they were 1.6% of a sweep's samples; docs/tier-cycle.md, "Survey: the lemmas and the allocator")
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
    /// `carry_chain_law`
    Chain,
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
fn vars(k: usize) -> Vec<Term> {
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
                    LawKind::Chain => "chain".into(),
                    LawKind::Tree => "tree".into(),
                };
                let law = shared_lemma(job, format!("{prover}_{}_{}_{n}_{k}", l.show(), r.show()), |job| match kind {
                    LawKind::Rule(name) => prove_rule(job, n, k, l, r).unwrap_or_else(|| panic!("rule {name} is not provable")),
                    LawKind::Assoc => add_assoc_proof(n, false),
                    LawKind::Comm => add_comm_proof(n, false),
                    LawKind::Bitwise => bitwise_law_k(n, k, l, r),
                    LawKind::Chain => carry_chain_law(n, l, r).expect("a constant carry"),
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

/// A sum of two (atom-abstracted) bitwise operands that a constant carry reduces to 0, -1 or one of its atoms (`x + 0`,
/// `x + ~x`, ...): the rewritten term and the plan, `carry_chain_law` at the atoms. Ablation name `chain`; it and a step for
/// `x + 0` alone covered each other (docs/tier-cycle.md, "Ablating the fixed rewriter and prover parts").
pub fn chain_step(job: &Job, a: &Term, b: &Term) -> Option<(Term, PlanRc)> {
    if job.setup().ablated("chain") {
        return None;
    }
    let mut atoms = vec![];
    let (a1, b1) = (abstract_atoms(a, &mut atoms, 2)?, abstract_atoms(b, &mut atoms, 2)?);
    // `carry_chain_law` proves every pair this finds: the atoms are add-free and at most two
    let cand = [Term::ZERO, Term::ONES, Term::v(0), Term::v(1)]
        .into_iter()
        .find(|cand| !matches!(*cand.node(), Node::V(i) if i >= atoms.len()) && find_constant_carry(&a1, &b1, cand).is_some())?;
    let target = if let Node::V(i) = *cand.node() { atoms[i] } else { cand };
    let args = (0..2).map(|i| atoms.get(i).cloned().unwrap_or(Term::v(0))).collect();
    Some((target, Plan::law(job, LawKind::Chain, Term::op(ADD, a1, b1), cand, args)))
}

/// A library law used as a left-to-right rewrite rule: `lhs = rhs` over the pattern variables `V(0)..`, each instance
/// proved from the law `add_tree_law` proves once (per width) for the patterns themselves. `name` is the `ABLATE` key.
pub struct Rule {
    pub name: &'static str,
    pub lhs: Term,
    pub rhs: Term,
}

/// What a job rewrites with (`Job::rules`, replaced only through `Job::with_rules`): the rule table and two switches.
/// Values, cheap to copy: the table is shared.
#[derive(Clone)]
pub struct Rules {
    /// The rules `rule_step` tries: the built-in ones, then those added at run time (by the rule miner) in `run_order`.
    table: Rc<RuleTable>,
    /// Set where a plan is only counted: by the rule miner's scoring rounds, by its rule-set evaluations under
    /// `RULEMINER_FAST=1` or when the caller asks, and by tests that count. `prove_eq` then takes a machine fallback when a
    /// few tuples agree, without searching for its carry encoding, so a plan made under it may not compile.
    score_only: bool,
    /// Print every rule application (the `normal_forms` debug test's `NF_TRACE`).
    trace_rules: bool,
}

impl Rules {
    /// The built-in rules of `setup` and the run-time rules `mined`, most specific first: larger left sides first, ties by
    /// text. `rule_step` applies the first rule that matches, so a library's order would otherwise change its normal forms:
    /// the same pooled library served in six orders gave total M 47-62 on add3 (docs/tier-cycle.md, "Rule order"). Any
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

/// A rule as its two sides, and a conflict between two rules (`Job::conflicts`): the one that rewrote a term, and a later
/// one that also matched it.
pub type RuleKey = (Term, Term);
pub type Conflict = (RuleKey, RuleKey);

/// `lhs -> rhs`, the spelling of rule files and logs.
pub fn rule_show((l, r): &RuleKey) -> String {
    format!("{} -> {}", l.show(), r.show())
}

/// A rule as `rule_step` tries it, with what does not depend on the term decided when the rule set is installed (deciding
/// it per term, and building the rule list per term, were about 10% of a sweep: docs/tier-cycle.md, "Profile at f447a57").
#[derive(Clone, Copy)]
pub(crate) struct TableRule {
    name: &'static str,
    lhs: Term,
    rhs: Term,
    /// the pattern variables of both sides are `V(0)..V(vars)`
    vars: usize,
    permutative: bool,
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
    fn key(&self) -> RuleKey {
        (self.lhs, self.rhs)
    }
}

/// Pattern variables a rule may have (`rule_weight` counts them in arrays this long).
const RULE_VARS: usize = 8;

/// A term's class as a rule pattern sees it: its operator, `0`, `-1` or a variable.
const CLASSES: usize = OP_INFO.len() + 3;

fn class(t: &Term) -> usize {
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
/// (docs/tier-cycle.md, "Per-thread refills and the miner's trace matching"); with the operands' classes alone, 31% of the
/// join's matcher calls failed at the grandchildren and 8.5% at a leaf ("Why the join's matches fail"), and with the shape
/// alone, 48% on a repeated variable within depth 2 ("Which repeated-variable failures the index could reject"). The
/// join's index carries each step's `Need`, so a step over the cap is skipped without loading the step.
struct PatIndex<K = ()> {
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
    fn new<'a>(pats: impl Iterator<Item = (usize, &'a Term, K)>) -> PatIndex<K> {
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
    fn get(&self, t: &Term) -> impl Iterator<Item = (usize, K)> + '_ {
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
    rules: Vec<TableRule>,
    index: PatIndex,
    join: Vec<JoinEq>,
    join_index: PatIndex<Need>,
    /// `join`'s steps by their law and direction (`lhs`, `rhs`, `backward`), the first of each, for `JoinStore`
    join_key: hashbrown::HashMap<(Term, Term, bool), u32>,
}

impl RuleTable {
    /// `new` with `mined` in `run_order` (`Rules::new`).
    fn sorted(setup: &Setup, mut mined: Vec<(Term, Term)>) -> RuleTable {
        mined.sort_by_cached_key(|(l, r)| run_order(l, r));
        RuleTable::new(setup, mined)
    }

    fn new(setup: &Setup, mined: Vec<(Term, Term)>) -> RuleTable {
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
    fn candidates(&self, t: &Term) -> impl Iterator<Item = (usize, &TableRule)> {
        self.index.get(t).map(|(i, ())| (i, &self.rules[i]))
    }
}

/// The run-time rules' order key (`RuleTable::sorted`).
pub fn run_order(l: &Term, r: &Term) -> (std::cmp::Reverse<usize>, String, String) {
    (std::cmp::Reverse(l.size()), l.show(), r.show())
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

#[test]
fn rule_order_does_not_change_rewriting() {
    let job = &Job::new(Setup::process());
    // overlapping rules: under list order the first one would win on sub(sub(x, y), z) whichever it is
    let a = "sub(sub(x, y), z) -> sub(x, add(y, z))\nsub(x, y) -> add(x, sub(0, y))\nsub(sub(x, y), z) -> sub(sub(x, z), y)\n";
    let b = "sub(sub(x, y), z) -> sub(sub(x, z), y)\nsub(x, y) -> add(x, sub(0, y))\nsub(sub(x, y), z) -> sub(x, add(y, z))\n";
    let installed = |text: &str| -> Vec<String> { Rules::new(job.setup(), parse_rules(text)).mined().iter().map(|(l, r)| format!("{} -> {}", l.show(), r.show())).collect() };
    let (ia, ib) = (installed(a), installed(b));
    assert_eq!(ia, ib);
    assert!(ia.last().unwrap().starts_with("sub(x, y)"), "the general rule goes after the specific ones: {ia:?}");
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
pub fn prove_rule(job: &mut Job, n: usize, k: usize, l: &Term, r: &Term) -> Option<(Expr, Expr)> {
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
fn proving<T>(job: &mut Job, blocked: &[RuleKey], f: impl FnOnce(&mut Job) -> T) -> T {
    let outer = job.blocked.len();
    job.blocked.extend(blocked.iter().cloned());
    let caller = std::mem::replace(&mut job.rw, RewriteState { budget: 10_000, ..Default::default() });
    let out = f(job);
    job.blocked.truncate(outer);
    job.rw = caller;
    out
}

/// A proof neither sees nor changes the caller's `rewrote` (Q4): before, it took the list over, so the terms the proof
/// took up joined it, or the proof's last rewrite cleared it.
#[test]
fn a_proof_leaves_the_callers_rewrote_alone() {
    let job = &mut Job::new(Setup::process());
    let t = parse_term("add(x, y)");
    job.rw.rewrote.push(t);
    let seen = proving(job, &[], |job| job.rw.rewrote.len());
    assert_eq!(seen, 0, "the proof starts with a list of its own");
    assert!(job.rw.rewrote.len() == 1 && job.rw.rewrote[0] == t, "the caller's list is as it was");
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
/// (docs/tier-cycle.md, "Per-thread refills and the miner's trace matching").
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

#[test]
fn unification_and_overlaps() {
    let t = parse_term;
    assert!(unify(&t("sub(sub(x, y), z)"), &t("sub(u, add(x, y))"), &mut vec![None; 8]));
    assert!(!unify(&t("x"), &t("add(x, y)"), &mut vec![None; 8]), "occurs check");
    assert!(!unify(&t("sub(x, x)"), &t("sub(0, -1)"), &mut vec![None; 8]), "a variable takes one value");
    // the two sub/sub orientations overlap at the root; sub(x, y) -> .. overlaps both below and at the root
    let rules = parse_rules("sub(sub(x, y), z) -> sub(x, add(y, z))\nsub(sub(x, y), z) -> sub(sub(x, z), y)\nlt(x, add(y, z)) -> lt(x, add(z, y))\n");
    let o = rule_overlaps(&rules);
    assert!(o.contains(&(0, 1, true)) && o.contains(&(1, 0, true)));
    assert!(o.contains(&(0, 0, false)), "sub(sub(x, y), z) also matches its own inner sub(x, y) position");
    assert!(!o.iter().any(|&(i, j, _)| (i == 2) != (j == 2)), "lt rules do not overlap sub rules: {o:?}");
}

/// `OVERLAP_RULES=<rules file>`: prints every overlapping pair of the file's rules and the counts.
#[test]
#[ignore]
fn rule_overlap_report() {
    let job = &Job::new(Setup::process());
    let rules = parse_rules(&std::fs::read_to_string(job.setup().var("OVERLAP_RULES").expect("set OVERLAP_RULES=<file>")).unwrap());
    let o = rule_overlaps(&rules);
    // a root overlap where one left side is an instance of the other is settled by specific-first order; the rest are not
    let inst = |a: &Term, b: &Term| match_pat(a, b, &mut vec![None; a.max_var() + 1]);
    let mut kinds = [0usize; 3];
    for &(i, j, root) in &o {
        let (li, lj) = (&rules[i].0, &rules[j].0);
        let kind = if !root { 0 } else if inst(li, lj) || inst(lj, li) { 1 } else { 2 };
        kinds[kind] += 1;
        println!("OVERLAP {} {} -> {}  WITH  {} -> {}", ["inner", "nested", "cross"][kind], li.show(), rules[i].1.show(), lj.show(), rules[j].1.show());
    }
    let touched: hashbrown::HashSet<usize> = o.iter().flat_map(|&(i, j, _)| [i, j]).collect();
    println!(
        "OVERLAPS {} rules, {} overlapping pairs: {} inner, {} at the root with one left side an instance of the other, {} at the root otherwise; {} rules in some overlap",
        rules.len(), o.len(), kinds[0], kinds[1], kinds[2], touched.len()
    );
}

pub fn subst_pat(p: &Term, sub: &[Option<Term>]) -> Term {
    match *p.node() {
        Node::V(i) => sub[i].expect("bound"),
        Node::Op(o, a, b) => Term::op(o, subst_pat(&a, sub), subst_pat(&b, sub)),
        _ => *p,
    }
}

/// Lists a job's rule conflicts (`Job::conflicts`), most terms first.
pub fn print_rule_conflicts(conflicts: Option<&hashbrown::HashMap<Conflict, u64>>) {
    if let Some(m) = conflicts {
        let mut v: Vec<_> = m.iter().map(|((w, l), c)| (rule_show(w), rule_show(l), *c)).collect();
        v.sort_by_key(|(w, l, c)| (std::cmp::Reverse(*c), w.clone(), l.clone()));
        for (w, l, c) in &v {
            println!("CONFLICT {c} {w}  WITH  {l}");
        }
        println!("CONFLICTS {} pairs, {} terms", v.len(), v.iter().map(|x| x.2).sum::<u64>());
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
        // a permutative rule (ordered rewriting): only when the instance goes down in the order on `show()` strings
        // (a path order on every tied instance, the removed `PERM_ORDER=lpo`, raised M, and the tie-break order before `show()`,
        // `PERM_ORDER=tie`, never became the default; the rewrite cycles both targeted are cut in `rewrite` instead: docs/tier-cycle.md)
        if r.permutative && inst.show_cmp(t).is_ge() {
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
    if let Some(m) = job.conflicts.as_mut() {
        for (_, r) in table.candidates(t).filter(|&(j, r)| j > i && fires(r).is_some()) {
            *m.entry((all[i].key(), r.key())).or_default() += 1;
        }
    }
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
/// without touching the terms (docs/tier-cycle.md, "Survey: the next lever").
#[derive(Clone, Default)]
pub struct Trace {
    items: Vec<(Term, Fired)>,
    shapes: u64,
}

impl Trace {
    pub fn new(items: Vec<(Term, Fired)>) -> Trace {
        let shapes = items.iter().fold(0, |m, (t, _)| m | t.shape());
        Trace { items, shapes }
    }

    pub fn items(&self) -> &[(Term, Fired)] {
        &self.items
    }

    /// Whether `rule` could act on some term of the trace on which `also` holds of the rule that fired: its left side matches it,
    /// or, on a term the join examined, its right side does where the rule is a join step backward (`join_usable`).
    pub fn touched_by(&self, (l, r): &(Term, Term), also: impl Fn(&Fired) -> bool) -> bool {
        let fits = |p: &Term| self.shapes & p.needs() == p.needs();
        let (fl, fr) = (fits(l), fits(r) && join_usable(r, l));
        (fl || fr) && self.items.iter().any(|(t, f)| (fl && matches(l, t) || fr && *f == Fired::Join && matches(r, t)) && also(f))
    }
}

/// Many traces' terms for `Trace::touched_by` over all of them at once: each distinct (term, fired) once, with the traces it
/// is in, grouped by the term's shape. The rule miner asks which of every law's traces each candidate touches (`affected`),
/// and the same terms recur across the laws' traces.
pub struct TraceIndex {
    groups: Vec<(u64, Vec<Indexed>)>,
}

/// A distinct trace item and the traces it is in, ascending.
type Indexed = (Term, Fired, Vec<usize>);

impl TraceIndex {
    pub fn new<'a>(traces: impl IntoIterator<Item = &'a Trace>) -> TraceIndex {
        let mut at: hashbrown::HashMap<(Term, Fired), Vec<usize>> = Default::default();
        for (i, tr) in traces.into_iter().enumerate() {
            for item in &tr.items {
                let v = at.entry(*item).or_default();
                if v.last() != Some(&i) {
                    v.push(i);
                }
            }
        }
        let mut groups: hashbrown::HashMap<u64, Vec<Indexed>> = Default::default();
        for ((t, f), v) in at {
            groups.entry(t.shape()).or_default().push((t, f, v));
        }
        TraceIndex { groups: groups.into_iter().collect() }
    }

    /// The traces, ascending, whose `touched_by(rule, also)` holds. A term's shape has every bit a pattern needs where the
    /// pattern matches it (`Term::shape`), so only those groups are scanned.
    pub fn touched(&self, (l, r): &(Term, Term), also: impl Fn(&Fired) -> bool) -> Vec<usize> {
        let back = join_usable(r, l);
        let (nl, nr) = (l.needs(), r.needs());
        let mut out = vec![];
        for (shape, items) in &self.groups {
            let (fl, fr) = (shape & nl == nl, back && shape & nr == nr);
            if !(fl || fr) {
                continue;
            }
            for (t, f, v) in items {
                if (fl && matches(l, t) || fr && *f == Fired::Join && matches(r, t)) && also(f) {
                    out.extend_from_slice(v);
                }
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }
}

/// A cached `rewrite`: the result and what the call did besides returning it, so that a hit can replay it.
struct Rewritten {
    out: (Term, PlanRc),
    /// rule steps used (`RewriteState::budget`): a hit needs at least this many left
    steps: i64,
    fallbacks: u64,
    /// the terms `rule_step` was asked about and whether a rule fired (`RewriteState::trace`), when `traced` (the trace was on)
    trace: Trace,
    traced: bool,
    /// the terms the call took up below its own (`RewriteState::rewrote`), once each: a replay is right only where the path cuts none of them
    rewrote: Vec<Term>,
}

/// While `Some`, `rewrite` calls over `k` variables are cached by (width, term). The rule miner sets it for one rule set
/// (one `score_laws` call): the result of `rewrite` is a function of the term, the rules in force and the budget left, so a repeat
/// under the same rules is a hit. Calls over other variable counts (the generalization path adds witnesses) are not cached.
/// `joins` caches `join_eq` by pair, with the trace that invalidates it: a failed search's examined terms, a met one's path.
pub struct RewriteMemo {
    k: usize,
    map: hashbrown::HashMap<(usize, Term), std::rc::Rc<Rewritten>>,
    joins: hashbrown::HashMap<(Term, Term), std::rc::Rc<Joined>>,
}

/// A memoized `join_eq`: its plan (`None` if the search failed) and its trace.
type Joined = (Option<PlanRc>, Trace);

impl RewriteMemo {
    pub fn new(k: usize) -> RewriteMemo {
        RewriteMemo { k, map: Default::default(), joins: Default::default() }
    }

    /// The traced entries whose traces `keep` accepts. A rule tried after the others changes no entry whose trace it matches
    /// nowhere among the terms no rule fired on, nor a join that examined no term it touches (`Trace::touched_by`), so the rule
    /// miner seeds each evaluation of a chosen set with the last one's entries that the rules in or out cannot change.
    pub fn filtered(&self, keep: impl Fn(&Trace) -> bool) -> RewriteMemo {
        // presized to the whole memo (an upper bound): grown from empty, the map rehashed several times per evaluation
        let mut map = hashbrown::HashMap::with_capacity(self.map.len());
        map.extend(self.map.iter().filter(|(_, e)| e.traced && keep(&e.trace)).map(|(k, e)| (*k, e.clone())));
        let mut joins = hashbrown::HashMap::with_capacity(self.joins.len());
        joins.extend(self.joins.iter().filter(|(_, e)| keep(&e.1)).map(|(k, e)| (*k, e.clone())));
        RewriteMemo { k: self.k, map, joins }
    }
}

/// The step budget one law gets in the probes, `law_cost` and the rewriting tests (`Job::measured`).
pub const LAW_STEPS: i64 = 200;
/// A budget no rewrite reaches: a job's own outside a measured call.
pub const UNBOUNDED: i64 = i64::MAX / 2;

/// A job's rewriting in progress (`Job::rw`). `proving` swaps in a fresh one for a rule's proof.
pub struct RewriteState {
    /// the terms `rewrite` is working on, outermost first
    pub path: Vec<Term>,
    /// the terms `rewrite` took up (pushed on the path) since the outermost call began, memo replays included
    pub rewrote: Vec<Term>,
    /// the lowest path index a cut matched since the innermost `rewrite_memo` miss began (`usize::MAX`: none)
    pub cut_low: usize,
    /// how many calls `rewrite` cut so far
    pub cycle_cuts: u64,
    pub memo: Option<RewriteMemo>,
    /// While `Some`, `rule_step` records every term it is asked to rewrite, and whether a rule fired on it: a rule added anywhere
    /// in the rule list can change a rewriting only if its left side matches one of them, and one added last only if it matches
    /// one where no rule fired.
    pub trace: Option<Vec<(Term, Fired)>>,
    /// How many more rule applications `rule_step` may make; the rule miner sets it per trial so that a candidate that
    /// undoes a built-in rule cannot loop. Soundness is unaffected: a refused step only leaves the term less normalized.
    pub budget: i64,
    /// How many times `prove_eq` closed a pair with a whole-term machine proof (the rewriting did not finish the job). Per
    /// job, so that the parallel miner's workers each read their own before/after difference.
    pub fallbacks: u64,
}

impl Default for RewriteState {
    fn default() -> RewriteState {
        RewriteState { path: vec![], rewrote: vec![], cut_low: usize::MAX, cycle_cuts: 0, memo: None, trace: None, budget: UNBOUNDED, fallbacks: 0 }
    }
}

/// `s` homeomorphically embeds in `t`: `t` is `s` with nodes inserted (Kruskal). Between terms of equal size it is equality.
fn embeds(s: &Term, t: &Term) -> bool {
    let couple = match (*s.node(), *t.node()) {
        (Node::V(i), Node::V(j)) => i == j,
        (Node::Zero, Node::Zero) | (Node::Ones, Node::Ones) => true,
        (Node::Op(f, s1, s2), Node::Op(g, t1, t2)) => f == g && embeds(&s1, &t1) && embeds(&s2, &t2),
        _ => false,
    };
    couple || matches!(*t.node(), Node::Op(_, t1, t2) if embeds(s, &t1) || embeds(s, &t2))
}

/// `t` (over `k` variables) rewritten bottom-up, with the plan of `t = t'` (`Compiler` proves it). Rewriting is deterministic apart from
/// the step budget, so a call `rewrite(t)` made while `t` itself is being rewritten further out can only repeat that work until the
/// budget runs out: a rewrite cycle. A chain that returns to a larger copy of a term it is rewriting (one that term embeds in) is
/// taken to grow without end. The cut returns `t` unchanged in both cases, so the chain ends one lap round instead of at the budget
/// (docs/tier-cycle.md, "Cycle cut").
pub fn rewrite(job: &mut Job, t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    if !matches!(*t.node(), Node::Op(..)) {
        return rewrite_memo(job, t, n, k);
    }
    if let Some(i) = cut_at(&job.rw.path, t) {
        job.rw.cut_low = job.rw.cut_low.min(i);
        job.rw.cycle_cuts += 1;
        return (*t, Plan::refl(job, t));
    }
    job.rw.path.push(*t);
    job.rw.rewrote.push(*t);
    let out = rewrite_memo(job, t, n, k);
    if job.rw.path.pop().is_some() && job.rw.path.is_empty() {
        job.rw.rewrote.clear();
    }
    out
}

/// The cycle cut's test: `t` repeats, or grows from, a term on `path`.
fn cut_by(path: &[Term], t: &Term) -> bool {
    cut_at(path, t).is_some()
}

/// The index of the innermost term on `path` that cuts `t`.
fn cut_at(path: &[Term], t: &Term) -> Option<usize> {
    let size = t.size();
    path.iter().rposition(|s| s.size() <= size && embeds(s, t))
}

fn rewrite_memo(job: &mut Job, t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    let on = matches!(*t.node(), Node::Op(..)) && job.rw.memo.as_ref().is_some_and(|m| m.k == k);
    if !on {
        return rewrite_uncached(job, t, n, k);
    }
    let key = (n, *t);
    let hit = job.rw.memo.as_ref().and_then(|m| m.map.get(&key).cloned());
    // the entry was made with no cut against a term further out, so the path in force now must cut none of the terms it took up
    // either; and one made while counting has no plan to give a caller that is not
    let counting = job.rules().score_only;
    let fits = |c: &Rewritten| {
        job.rw.budget >= c.steps
            && (counting || !matches!(*c.out.1, Plan::Counting))
            && !c.rewrote.iter().any(|v| cut_by(&job.rw.path, v))
    };
    if let Some(c) = hit.filter(|c| fits(c)) {
        if cfg!(debug_assertions) {
            check_replay(job, t, n, k, &c);
        }
        job.rw.budget -= c.steps;
        job.rw.fallbacks += c.fallbacks;
        if let Some(v) = job.rw.trace.as_mut() {
            v.extend_from_slice(c.trace.items());
        }
        job.rw.rewrote.extend(c.rewrote.iter().copied());
        return c.out.clone();
    }
    let (budget0, fallbacks0, trace0) = (job.rw.budget, job.rw.fallbacks, job.rw.trace.as_ref().map(|v| v.len()));
    let (plen, low0, rewrote0) = (job.rw.path.len(), std::mem::replace(&mut job.rw.cut_low, usize::MAX), job.rw.rewrote.len());
    let out = rewrite_uncached(job, t, n, k);
    let (budget1, low) = (job.rw.budget, job.rw.cut_low);
    job.rw.cut_low = low0.min(low);
    // a call that ran the budget out was cut short by it: its result depends on the budget it started with. One with a cycle cut
    // against a term further out than `t` (`rewrite` pushed `t` at `plen - 1`) depends on that term; cuts against `t` or terms
    // taken up below it come back on any replay, and no new cut can, since a path that cuts a term in `rewrote` is never replayed
    if budget1 > 0 && low.saturating_add(1) >= plen {
        let trace = Trace::new(job.rw.trace.as_ref().map(|v| v[trace0.unwrap_or(0)..].to_vec()).unwrap_or_default());
        // once each, in address order (a replay only asks whether the path cuts any of them); a fresh set per entry grew and
        // rehashed for 2.2% of a sweep (docs/tier-cycle.md, "Survey: the next lever")
        let mut rewrote = job.rw.rewrote[rewrote0..].to_vec();
        rewrote.sort_unstable_by_key(|t| t.addr());
        rewrote.dedup();
        let entry = Rewritten { out: out.clone(), steps: budget0 - budget1, fallbacks: job.rw.fallbacks - fallbacks0, trace, traced: trace0.is_some(), rewrote };
        if let Some(m) = job.rw.memo.as_mut() {
            m.map.insert(key, std::rc::Rc::new(entry));
        }
    }
    out
}

/// Debug builds: a memo hit about to be replayed is redone without the memo, under the same path and budget, and must match it
/// (the law 168 bug was a replay a fresh rewrite would have cut). Only `Job::conflicts` keeps the redo's counts. Release
/// builds compile it too, so it cannot rot unseen.
fn check_replay(job: &mut Job, t: &Term, n: usize, k: usize, c: &Rewritten) {
    let memo = std::mem::take(&mut job.rw.memo);
    let trace = std::mem::take(&mut job.rw.trace);
    let (budget, fallbacks, cuts, low, rewrote) = (
        job.rw.budget,
        job.rw.fallbacks,
        job.rw.cycle_cuts,
        job.rw.cut_low,
        job.rw.rewrote.len(),
    );
    let fresh = rewrite_uncached(job, t, n, k);
    let (steps, fresh_fallbacks) = (budget - job.rw.budget, job.rw.fallbacks - fallbacks);
    job.rw.memo = memo;
    job.rw.trace = trace;
    job.rw.budget = budget;
    job.rw.fallbacks = fallbacks;
    job.rw.cycle_cuts = cuts;
    job.rw.cut_low = low;
    job.rw.rewrote.truncate(rewrote);
    let show = |(t, s, f): (Term, i64, u64)| format!("{} in {s} steps, {f} fallbacks", t.show());
    assert!(
        (fresh.0, steps, fresh_fallbacks) == (c.out.0, c.steps, c.fallbacks),
        "memo replay of {}: {} where a fresh rewrite gives {}",
        t.show(),
        show((c.out.0, c.steps, c.fallbacks)),
        show((fresh.0, steps, fresh_fallbacks))
    );
}

fn rewrite_uncached(job: &mut Job, t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    let Node::Op(o, a, b) = *t.node() else { return (*t, Plan::refl(job, t)) };
    // children first: trying the library rules on a node before its children are normalized raised M 3x (docs/tier-cycle.md, "Rule order")
    let ((a2, pa), (b2, pb)) = (rewrite(job, &a, n, k), rewrite(job, &b, n, k));
    let cong = Plan::cong(job, o, pa, pb);
    let t1 = Term::op(o, a2, b2);
    // the class table's normal form (docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md §5): a node the
    // table knows is final, as its own representative or through the proved step to it; any other node goes on to the
    // rules (over a fourth variable, a class not stored, or a replacement with no proof)
    if !job.setup().ablated("classes") {
        let c = crate::classes::Classes::get();
        if let Some(r) = c.lookup(&t1) {
            if r == t1 {
                return (t1, cong);
            }
            if let Some((r, p)) = c.step(job, n, k, &t1) {
                return (r, Plan::trans(job, cong, p));
            }
        }
    }
    if o != ADD {
        // the library rules first (`shldist`, ...)
        if let Some((target, step)) = rule_step(job, &t1) {
            let (t3, p3) = rewrite(job, &target, n, k);
            return (t3, Plan::trans(job, Plan::trans(job, cong, step), p3));
        }
        if matches!(o, SUB | LT | SHL1 | SHR1) {
            return (t1, cong);
        }
        // bitwise and shift terms only: a node equal to 0, -1 or one of its own subterms collapses to it, by the
        // per-position prover (the truth-table collapse below treats a shift as an atom)
        if let (false, true, true) = (job.setup().ablated("collapse"), t1.add_free(), t1.has_shift()) {
            let mut subs = vec![];
            t1.subterms(&mut subs);
            let cands = [Term::ZERO, Term::ONES].into_iter().chain(subs.into_iter().skip(1).filter(|c| c.size() < t1.size()));
            if let Some(c) = cands.into_iter().find(|c| c.add_free() && t1.is_law(c, k)) {
                return (c, Plan::trans(job, cong, Plan::law(job, LawKind::Bitwise, t1, c, vars(k))));
            }
        }
        // a bitwise node equal to 0, -1 or one of its atoms collapses to it (truth table, then `bitwise_law`)
        let mut atoms = vec![];
        if let (false, Some(abs)) = (job.setup().ablated("collapse"), abstract_atoms(&t1, &mut atoms, k)) {
            let truth = |t: &Term| (0..1usize << k).map(|m| term_gb(&Bools, t, &(0..k).map(|v| m >> v & 1 == 1).collect::<Vec<_>>())).collect::<Vec<_>>();
            let want = truth(&abs);
            let cands: Vec<Term> = [Term::ZERO, Term::ONES].into_iter().chain((0..k).map(Term::v)).collect();
            if let Some(c) = cands.iter().find(|c| c.max_var() < atoms.len().max(1) && truth(c) == want) {
                let target = if let Node::V(i) = *c.node() { atoms[i] } else { *c };
                if target != t1 {
                    let args = (0..k).map(|i| atoms.get(i).cloned().unwrap_or(Term::v(0))).collect();
                    return (target, Plan::trans(job, cong, Plan::law(job, LawKind::Bitwise, abs, *c, args)));
                }
            }
        }
        // commutative operands in a fixed order (text order, constants last: 0 before -1), by the generic bitwise law
        let constant = |t: &Term| match *t.node() {
            Node::Zero => Some(0),
            Node::Ones => Some(1),
            _ => None,
        };
        let before = match (constant(&b2), constant(&a2)) {
            (None, None) => b2.show_cmp(&a2).is_lt(),
            (None, Some(_)) => true,
            (Some(_), None) => false,
            (Some(cb), Some(ca)) => cb < ca,
        };
        if before {
            let swap = |x: Term, y: Term| Term::op(o, x, y);
            let law = Plan::law(job, LawKind::Bitwise, swap(Term::v(0), Term::v(1)), swap(Term::v(1), Term::v(0)), vec![a2, b2]);
            return (swap(b2, a2), Plan::trans(job, cong, law));
        }
        return (t1, cong);
    }
    let sum = |p: &Term, q: &Term| Term::op(ADD, *p, *q);
    let (x, y, z) = (Term::v(0), Term::v(1), Term::v(2));
    let assoc = |job: &Job, p: &Term, q: &Term, r: &Term| Plan::law(job, LawKind::Assoc, sum(&sum(&x, &y), &z), sum(&x, &sum(&y, &z)), vec![*p, *q, *r]);
    let comm = |job: &Job, p: &Term, q: &Term| Plan::law(job, LawKind::Comm, sum(&x, &y), sum(&y, &x), vec![*p, *q]);
    // `x + 0` and `x + ~x` are constant-carry sums (`chain_step`); steps of their own were removed as redundant
    let step = if let Some(r) = rule_step(job, &t1) {
        Some(r)
    } else if let Some(r) = chain_step(job, &a2, &b2) {
        Some(r)
    } else if let (false, Node::Op(ADD, p, q)) = (job.setup().ablated("assoc"), *a2.node()) {
        // (p + q) + r = p + (q + r)
        Some((sum(&p, &sum(&q, &b2)), assoc(job, &p, &q, &b2)))
    } else if let (false, Node::Op(ADD, bp, bq)) = (job.setup().ablated("assoc") || job.setup().ablated("comm"), *b2.node()) {
        if bp.show_cmp(&a2).is_lt() {
            // a + (b + c) = (a + b) + c = (b + a) + c = b + (a + c)
            let (a_, b_, c_) = (&a2, &bp, &bq);
            let swapped = Plan::cong(job, ADD, comm(job, a_, b_), Plan::refl(job, c_));
            Some((sum(b_, &sum(a_, c_)), Plan::trans(job, Plan::trans(job, Plan::sym(job, assoc(job, a_, b_, c_)), swapped), assoc(job, b_, a_, c_))))
        } else {
            None
        }
    } else if !job.setup().ablated("comm") && b2.show_cmp(&a2).is_lt() {
        Some((sum(&b2, &a2), comm(job, &a2, &b2)))
    } else {
        None
    };
    match step {
        None => (t1, cong),
        Some((t2, p)) => {
            let (t3, p3) = rewrite(job, &t2, n, k);
            (t3, Plan::trans(job, Plan::trans(job, cong, p), p3))
        }
    }
}

/// `t` with each variable and each `add` subterm replaced by an atom variable (up to `cap`, by `show`).
pub fn abstract_atoms(t: &Term, atoms: &mut Vec<Term>, cap: usize) -> Option<Term> {
    match *t.node() {
        Node::Zero | Node::Ones => Some(*t),
        Node::V(_) | Node::Op(ADD | SUB | SHL1 | SHR1, ..) => {
            let i = match atoms.iter().position(|a| a == t) {
                Some(i) => i,
                None => {
                    atoms.push(*t);
                    atoms.len() - 1
                }
            };
            (i < cap).then_some(Term::v(i))
        }
        Node::Op(o, a, b) => Some(Term::op(o, abstract_atoms(&a, atoms, cap)?, abstract_atoms(&b, atoms, cap)?)),
    }
}

/// The join's searches run (`join_search`), the terms they reached, how many met, the memo hits that ran none, and the
/// time in the searches, of it in those that failed; the joins `JoinStore` served, and the time in its queries (served
/// or not).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct JoinCost {
    pub searches: u64,
    pub reached: u64,
    pub met: u64,
    pub hits: u64,
    pub nanos: u64,
    pub failed_nanos: u64,
    pub stored: u64,
    pub store_nanos: u64,
}

impl JoinCost {
    /// the counts from `before` to `self` (a job's `join_cost` at two times)
    pub fn since(self, before: JoinCost) -> JoinCost {
        self.zip(before, |a, b| a - b)
    }

    /// `other`'s counts added to these
    pub fn add(&mut self, other: JoinCost) {
        *self = self.zip(other, |a, b| a + b);
    }

    fn zip(self, o: JoinCost, f: impl Fn(u64, u64) -> u64) -> JoinCost {
        JoinCost {
            searches: f(self.searches, o.searches),
            reached: f(self.reached, o.reached),
            met: f(self.met, o.met),
            hits: f(self.hits, o.hits),
            nanos: f(self.nanos, o.nanos),
            failed_nanos: f(self.failed_nanos, o.failed_nanos),
            stored: f(self.stored, o.stored),
            store_nanos: f(self.store_nanos, o.store_nanos),
        }
    }
}

/// A join step `JoinStore` keeps: the step at `path` from `from` by the law `lhs = rhs` read in direction `backward`, which
/// a table holds under that key (`RuleTable::join_key`) whatever its index.
#[derive(Clone, Copy)]
struct StoredStep {
    from: Term,
    path: StepPath,
    law: (Term, Term, bool),
}

/// The steps of the join's met paths, as edges between the terms they join: each term's neighbours, by the step and
/// whether it is walked backwards. A path through steps whose laws the current table holds proves its ends equal, so
/// `join_eq` serves a pair from the store before it searches. The miner keeps one per mine, fed by its main thread's
/// searches with the memo on (not its proofs, which run on that thread only at some thread counts); its workers read a
/// copy frozen when a round of scoring starts, so a candidate's gain depends neither on the thread count nor on which
/// worker scored what (docs/tier-cycle.md, "Spike of the join store"). The copy is the whole store, once a round.
#[derive(Clone, Default)]
pub struct JoinStore {
    edges: hashbrown::HashMap<Term, Vec<StoredEdge>>,
}

/// An edge of `JoinStore` from the term it is kept under: to `to` by `step`, walked backwards (from `step`'s result to
/// `step.from`) if `back`.
#[derive(Clone, Copy)]
struct StoredEdge {
    to: Term,
    step: StoredStep,
    back: bool,
}

/// How a thread uses a join store: feeding it from its met searches and reading it, or reading a frozen copy.
pub enum JoinStoreUse {
    Feed(JoinStore),
    Read(std::sync::Arc<JoinStore>),
}

impl JoinStoreUse {
    /// A frozen copy of the store this use feeds, for the jobs that read it; `None` for a reader.
    pub fn frozen(&self) -> Option<std::sync::Arc<JoinStore>> {
        match self {
            JoinStoreUse::Feed(store) => Some(std::sync::Arc::new(store.clone())),
            JoinStoreUse::Read(_) => None,
        }
    }

    fn store(&self) -> &JoinStore {
        match self {
            JoinStoreUse::Feed(store) => store,
            JoinStoreUse::Read(store) => store,
        }
    }
}

impl JoinStore {
    fn add(&mut self, to: Term, step: StoredStep) {
        let v = self.edges.entry(step.from).or_default();
        if !v.iter().any(|e| e.to == to && e.step.law == step.law && e.step.path == step.path) {
            v.push(StoredEdge { to, step, back: false });
            self.edges.entry(to).or_default().push(StoredEdge { to: step.from, step, back: true });
        }
    }
    /// The plan of `a = b` along the shortest stored path through the job's laws and terms of at most `cap` nodes, looked
    /// for among `join_visit()` terms at most, as the search, and the path's terms.
    fn path(&self, job: &Job, a: Term, b: Term, cap: usize) -> Option<(PlanRc, Vec<Term>)> {
        let table = &*job.rules().table;
        let mut prev: hashbrown::HashMap<Term, Option<(Term, StoredStep, bool, u32)>> = [(a, None)].into_iter().collect();
        let (mut front, visit) = (vec![a], join_visit(job));
        // bounded by the terms reached, as the search is (here checked once a layer)
        while !front.is_empty() && prev.len() <= visit {
            for t in std::mem::take(&mut front) {
                for &StoredEdge { to: u, step, back } in self.edges.get(&t).into_iter().flatten() {
                    let Some(&eq) = table.join_key.get(&step.law) else { continue };
                    if u.size() > cap || prev.contains_key(&u) {
                        continue;
                    }
                    prev.insert(u, Some((t, step, back, eq)));
                    if u == b {
                        // back from `b`: each step's plan, `p = x` read forwards
                        let (mut plans, mut terms, mut x) = (vec![], vec![b], b);
                        while let Some((p, step, back, eq)) = prev[&x] {
                            let plan = step_plan(job, &JoinStep { from: step.from, path: step.path, eq });
                            plans.push(if back { Plan::sym(job, plan) } else { plan });
                            terms.push(p);
                            x = p;
                        }
                        return Some((plans.into_iter().rev().reduce(|a, b| Plan::trans(job, a, b)).expect("a step"), terms));
                    }
                    front.push(u);
                }
            }
        }
        None
    }
}

/// The plan of `a = b` from the job's join store under the current table, and the path's terms.
fn stored_join(job: &Job, a: Term, b: Term) -> Option<(PlanRc, Vec<Term>)> {
    let cap = a.size().max(b.size()) + 2;
    job.join_store.as_ref()?.store().path(job, a, b, cap)
}

/// `t` with every occurrence of the subterm `x` replaced by `with`.
pub fn replace_term(t: &Term, x: &Term, with: &Term) -> Term {
    if t == x {
        return *with;
    }
    match *t.node() {
        Node::Op(o, a, b) => Term::op(o, replace_term(&a, x, with), replace_term(&b, x, with)),
        _ => *t,
    }
}

/// The plan of `a = b` (over `k` variables) for rewritten terms: `refl`; the bitwise law over atoms (when it holds on all
/// bit values, so the kernel check cannot fail); the per-position law; the class table's normal forms (when both sides
/// meet); the bit-0 mask reduction; or the whole-term machine
/// proof. `None` otherwise.
pub fn prove_eq(job: &mut Job, n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    if a == b {
        return Some(Plan::refl(job, a));
    }
    // each step below can be switched off: `ABLATE=eq_truth,eq_pos,eq_classes,shrmask`
    let mut atoms = vec![];
    if let (false, Some(a1), Some(a2)) = (job.setup().ablated("eq_truth"), abstract_atoms(a, &mut atoms, k), abstract_atoms(b, &mut atoms, k)) {
        let holds = (0..1usize << k).all(|m| {
            let bits: Vec<bool> = (0..k).map(|v| m >> v & 1 == 1).collect();
            term_gb(&Bools, &a1, &bits) == term_gb(&Bools, &a2, &bits)
        });
        if holds {
            let args = (0..k).map(|i| atoms.get(i).cloned().unwrap_or(Term::v(0))).collect();
            return Some(Plan::law(job, LawKind::Bitwise, a1, a2, args));
        }
    }
    // add-free terms with shifts: the per-position prover, when the law holds exhaustively at widths 1..=5 (a position
    // reads only a few neighbours, so widths this small contain every case; the kernel checks the proof regardless)
    if !job.setup().ablated("eq_pos") && k <= 3 && a.add_free() && b.add_free() && (a.has_shift() || b.has_shift()) {
        let holds = (1..=5usize).all(|w| (0..1u128 << (w * k)).all(|i| {
            let vals: Vec<u128> = (0..k).map(|v| (i >> (w * v)) & low_bits(w)).collect();
            a.interp(w, &vals) == b.interp(w, &vals)
        }));
        if holds {
            return Some(Plan::law(job, LawKind::Bitwise, *a, *b, vars(k)));
        }
    }
    // the learned class table (docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md §4): both sides
    // normalized by its proved replacements; if they meet, the law is closed with no rule, and only then are its steps
    // counted (`Job::steps_if_closed`)
    if !job.setup().ablated("eq_classes") {
        let c = crate::classes::Classes::get();
        let closed = job.steps_if_closed(|job| {
            let ((na, pa), (nb, pb)) = (c.normalize(job, n, k, a), c.normalize(job, n, k, b));
            (na == nb).then(|| Plan::trans(job, pa, Plan::sym(job, pb)))
        });
        if closed.is_some() {
            return closed;
        }
    }
    // congruence on equal operators and generalizing a shared subterm into a variable were removed: neither decided a law
    // (docs/tier-cycle.md, "Ablating the fixed rewriter and prover parts")
    if let Some(p) = shr_mask_eq(job, n, k, a, b) {
        return Some(p);
    }
    join_or_machine(job, n, k, a, b)
}

/// The whole-term machine proof of `a = b` (the carry-encoding proof for the two terms as bit-serial machines), counted in
/// `RewriteState::fallbacks`; `None` when there is none.
fn machine_fallback(job: &mut Job, n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    let cost = |t: &Term| Machine::parse(t).map_or(0, |m| m.carries());
    // scoring mode: only whether the rewriting needed this fallback matters, so count it without searching for the encoding (the
    // plan may then not compile); a pair that is not equal fails here as it would in `tree_encoding` (else congruence on unequal
    // operands would count two proofs); a few tuples suffice to tell, since unequal pairs differ almost everywhere
    let screened = job.rules().score_only && Machine::parse(a).is_some() && Machine::parse(b).is_some() && cost(a).max(cost(b)) <= carry_cap(job);
    if screened && a.differs_in(b, n, k, 16) || !screened && tree_encoding(job, n, k, a, b).is_none() {
        return None;
    }
    job.rw.fallbacks += 1;
    Some(Plan::law(job, LawKind::Tree, *a, *b, vars(k)))
}

/// `a = b` by the bounded join, else by the whole-term machine proof: the floor laws' normal forms all join within a few
/// equation steps (docs/tier-cycle.md, "Equational reach of the floor").
fn join_or_machine(job: &mut Job, n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    join_eq(job, n, k, a, b).or_else(|| machine_fallback(job, n, k, a, b))
}

/// One step the join may take: `from -> to` over the pattern variables `V(0..vars)`, an instance of the proved law
/// `lhs = rhs` of `kind` (read right to left when `backward`).
#[derive(Clone, Copy)]
struct JoinEq {
    from: Term,
    to: Term,
    vars: usize,
    kind: LawKind,
    lhs: Term,
    rhs: Term,
    backward: bool,
    need: Need,
}

/// How many nodes a join step needs, found without matching, so `join_walk` skips a step over the cap unmatched. When every
/// variable occurs in `to` at least as often as in `from`, the step at `t` has `size(t) + size(to) - size(from)` nodes or
/// more (each binding is counted in `to` at least as often as in `t`): it needs that growth from the room the cap leaves
/// above `size(t)`. Otherwise each variable binds at least one node, so it needs `size(to)` of the cap (`of_cap`). 43% of
/// the join's matcher calls have a bound over the cap (docs/tier-cycle.md, "How much the size bound would skip").
#[derive(Clone, Copy, Debug)]
struct Need {
    nodes: isize,
    of_cap: bool,
}

impl Need {
    fn skips(self, room: isize, cap: isize) -> bool {
        self.nodes > if self.of_cap { cap } else { room }
    }
}

impl JoinEq {
    fn new(from: Term, to: Term, vars: usize, kind: LawKind, lhs: Term, rhs: Term, backward: bool) -> JoinEq {
        let (mut of, mut ot) = ([0; RULE_VARS], [0; RULE_VARS]);
        (from.occurrences(&mut of), to.occurrences(&mut ot));
        let need = match of.iter().zip(&ot).all(|(f, t)| t >= f) {
            true => Need { nodes: to.size() as isize - from.size() as isize, of_cap: false },
            false => Need { nodes: to.size() as isize, of_cap: true },
        };
        JoinEq { from, to, vars, kind, lhs, rhs, backward, need }
    }
}

/// Whether `from -> to` can be a join step: `from` is not a bare variable, binds every variable of `to`, and keeps `lt` at the
/// root (`lt` occurs nowhere else).
fn join_usable(from: &Term, to: &Term) -> bool {
    let is_lt = |t: &Term| matches!(*t.node(), Node::Op(LT, ..));
    !matches!(*from.node(), Node::V(_)) && (0..RULE_VARS).all(|v| !to.has_var(v) || from.has_var(v)) && is_lt(from) == is_lt(to)
}

/// The join's steps: every rule not ablated (built-in, promoted and mined), add's associativity and commutativity and those of
/// and, or and xor, each rule and associativity both ways where `join_usable`.
fn join_eqs(setup: &Setup, rules: &[TableRule]) -> Vec<JoinEq> {
    let (x, y, z) = (Term::v(0), Term::v(1), Term::v(2));
    let op = Term::op;
    let mut laws: Vec<(LawKind, Term, Term, bool)> = rules.iter().filter(|r| !setup.ablated(r.name)).map(|r| (LawKind::Rule(r.name), r.lhs, r.rhs, true)).collect();
    laws.push((LawKind::Assoc, op(ADD, op(ADD, x, y), z), op(ADD, x, op(ADD, y, z)), true));
    laws.push((LawKind::Comm, op(ADD, x, y), op(ADD, y, x), false));
    for o in [AND, OR, XOR] {
        laws.push((LawKind::Bitwise, op(o, op(o, x, y), z), op(o, x, op(o, y, z)), true));
        laws.push((LawKind::Bitwise, op(o, x, y), op(o, y, x), false));
    }
    let mut eqs = vec![];
    for (kind, lhs, rhs, both) in laws {
        let vars = lhs.max_var().max(rhs.max_var()) + 1;
        for (from, to, backward) in [(lhs, rhs, false), (rhs, lhs, true)] {
            if (both || !backward) && join_usable(&from, &to) {
                eqs.push(JoinEq::new(from, to, vars, kind, lhs, rhs, backward));
            }
        }
    }
    eqs
}

/// After a step, `join_walk` skips the subtrees left of the step's path: there a step and this one, the other
/// taken first, would reach the same term. Its ancestors, the rewritten subterm and what is right of it stay.
#[test]
fn join_walk_after_a_step_skips_the_subtrees_left_of_its_path() {
    // the step rewrote `c` in `add(and(a, b), or(c, d))`: right at the root, then left
    let t = parse_term("add(and(x, y), or(xor(x, y), sub(y, x)))");
    let table = RuleTable::new(&Setup::process(), vec![]);
    let walked = |order: Option<StepPath>| {
        let mut examined = Some(hashbrown::HashSet::default());
        join_walk(t, order, &table, &[], 1000, &mut vec![], &mut examined, &mut |_, _, _, _, _| true);
        let mut v: Vec<String> = examined.unwrap().into_iter().map(|t| t.show()).collect();
        v.sort();
        v
    };
    let mut all = vec![];
    t.subterms(&mut all);
    let mut want: Vec<String> = all.iter().map(|t| t.show()).collect::<std::collections::BTreeSet<_>>().into_iter().collect();
    assert_eq!(walked(None), want);
    // `and(x, y)` is left of the path; `x` and `y` stay, as subterms of the right side too
    want.retain(|s| s != "and(x, y)");
    assert_eq!(walked(Some(StepPath { path: 0b01, depth: 2 })), want);
    // a step at the root leaves nothing to its left
    assert_eq!(walked(Some(StepPath { path: 0, depth: 0 })).len(), want.len() + 1);
}

/// A step orders the walk after it only when it did not shrink the term: then the other order's middle term is no larger
/// than the end term, so within the cap whenever the end term is.
#[test]
fn a_join_step_orders_the_walk_after_it_only_when_it_did_not_shrink_the_term() {
    let (from, path) = (parse_term("add(and(x, y), add(z, 0))"), StepPath { path: 0b1, depth: 1 });
    let step = JoinStep { from, path, eq: 0 };
    let ordered = |to: &str| step.order(parse_term(to)).map(|p| (p.path, p.depth));
    assert_eq!(ordered("add(and(x, y), z)"), None, "the step shrank the term");
    assert_eq!(ordered("add(and(x, y), add(0, z))"), Some((0b1, 1)), "same size");
    assert_eq!(ordered("add(and(x, y), add(z, add(0, 0)))"), Some((0b1, 1)), "grew");
}

/// `Need::skips` skips a match only when its step is over the cap, and every match over the cap for a rule that repeats
/// no variable, such as commutativity: so `join_walk` skipping by it changes no search.
#[test]
fn join_need_skips_only_steps_over_the_cap() {
    let job = &Job::new(Setup::process());
    let rule = |l: &str, r: &str| TableRule { name: "t", lhs: parse_term(l), rhs: parse_term(r), vars: 2, permutative: false };
    let eqs = join_eqs(job.setup(), &[rule("and(x, or(x, y))", "x"), rule("add(x, x)", "shl1(x, 0)"), rule("xor(x, y)", "xor(y, xor(x, 0))")]);
    let mut terms = vec![Term::v(0), Term::v(1), Term::ZERO];
    for _ in 0..2 {
        let level: Vec<Term> = terms.iter().flat_map(|&a| terms.iter().flat_map(move |&b| [ADD, AND, OR, XOR, SHL1].map(|o| Term::op(o, a, b)))).collect();
        terms.extend(level);
    }
    let (mut matched, mut exact) = (0, 0);
    for e in &eqs {
        for &t in &terms {
            let mut sub = [None; RULE_VARS];
            if match_pat(&e.from, &t, &mut sub) {
                let size = subst_sig(&e.to, &sub).1;
                let skips: Vec<bool> = (0..size + 3).map(|cap| e.need.skips(cap as isize - t.size() as isize, cap as isize)).collect();
                for (cap, &s) in skips.iter().enumerate() {
                    assert!(!s || size > cap, "{} -> {} at {}: skipped at cap {cap}, step {size}", e.from.show(), e.to.show(), t.show());
                }
                matched += 1;
                exact += (matches!(e.kind, LawKind::Comm) && skips.iter().enumerate().all(|(cap, &s)| s == (size > cap))) as usize;
            }
        }
    }
    assert!(matched > 1000 && exact > 100, "matched {matched}, exact for add's commutativity {exact}");
}


/// How many terms the join reaches at most, `JOIN_VISIT` (1000): its searches and `JoinStore`'s queries.
fn join_visit(job: &Job) -> usize {
    job.setup().or("JOIN_VISIT", 1000)
}

/// The plan of `a = b` by joining them: from both at once over `join_eqs`, the side with fewer pending terms expanding its
/// one with the least depth plus size (a step that grows the term by a node costs 2, a same-size one 1, one that shrinks
/// it by a node 0; against breadth-first, a lower stream M for about a third less CPU: docs/tier-cycle.md, "Depth plus
/// size on the sweep"), through terms of at most the larger side's size plus 2 nodes, until the two reached sets meet or
/// more than `JOIN_VISIT` (1000) terms are reached (5000 left a few laws fewer to the machine proof for 2-3 times the sweep time:
/// docs/tier-cycle.md, "The bounded join removes the floor"). Only pairs equal on random inputs are searched, so an unequal
/// pair costs no search. `ABLATE=join` switches it off. With the memo on, a pair the job's `JoinStore` has a path for
/// is served from it without a search (77% of a cold:cmp3d mine's searches: docs/tier-cycle.md, "Spike of the join store").
/// The terms it examined go to `RewriteState::trace` (`Fired::Join`) and, with the result, to `RewriteState::memo`'s `joins`, so the rule
/// miner reuses it as it does a rewrite: a failed search, all of them (under other rules it is the same search when no rule
/// in or out touches them), served only while the store has no path for the pair; a met one, the terms on its path and their subterms, where the rules its plan used fired (the
/// plan stays a proof while no rule it used is removed, so rules added elsewhere keep it). That is inexact where added rules
/// would push the search over `JOIN_VISIT` before it meets: the
/// cap makes the join non-monotone in its rules, and no rule-independent cap tried was as strong at the same cost
/// (docs/decisions/2026-10-17-monotone-join.md).
pub fn join_eq(job: &mut Job, n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    if job.setup().ablated("join") || a.differs_in(b, n, k, 16) {
        return None;
    }
    // the memo holds searches with no rule blocked (`Job::blocked`), and a plan made while counting serves only a caller that counts
    let memo_on = job.rw.memo.as_ref().is_some_and(|m| m.k == k) && job.blocked.is_empty();
    let traced = job.rw.trace.is_some();
    let counting = job.rules().score_only;
    let key = (*a, *b);
    let replay = |job: &mut Job, trace: &Trace| {
        if let Some(v) = job.rw.trace.as_mut() {
            v.extend_from_slice(trace.items());
        }
    };
    let stored = |job: &mut Job| {
        let t0 = std::time::Instant::now();
        let s = stored_join(job, *a, *b);
        job.join_cost.store_nanos += t0.elapsed().as_nanos() as u64;
        s
    };
    let mut from_store = None;
    if memo_on {
        let hit = job.rw.memo.as_ref().and_then(|m| m.joins.get(&key).cloned());
        if let Some(e) = hit.filter(|e| counting || e.0.as_ref().is_none_or(|p| !matches!(**p, Plan::Counting))) {
            // a failed search stands only while the store has no path for the pair: the store grows as searches feed it
            // (`a_cached_failed_join_yields_to_a_stored_path`)
            from_store = if e.0.is_none() { stored(job) } else { None };
            if from_store.is_none() {
                replay(job, &e.1);
                job.join_cost.hits += 1;
                return e.0.clone();
            }
        }
    }
    let mut examined = (memo_on || traced).then(hashbrown::HashSet::<Term>::default);
    let stored = if from_store.is_some() { from_store } else if memo_on { stored(job) } else { None };
    job.join_cost.stored += stored.is_some() as u64;
    let found = match stored {
        // a stored path's result rests on its terms, as a met search's on its path's: they and their subterms
        Some((plan, mut stack)) => {
            if let Some(x) = &mut examined {
                while let Some(q) = stack.pop() {
                    if let (true, Node::Op(_, l, r)) = (x.insert(q), *q.node()) {
                        stack.extend([l, r]);
                    }
                }
            }
            Some(plan)
        }
        // fed only where read, so what proofs search (memo off or a rule blocked) never reaches it
        None => join_search(job, a, b, &mut examined, memo_on),
    };
    if let Some(x) = examined {
        let trace = Trace::new(x.into_iter().map(|t| (t, Fired::Join)).collect());
        replay(job, &trace);
        if memo_on {
            job.rw.memo.as_mut().map(|m| m.joins.insert(key, std::rc::Rc::new((found.clone(), trace))));
        }
    }
    found
}

/// The path to the subterm a join step is at: `depth` children down, going right at depth `i` where bit `i` of `path`
/// is set.
#[derive(Clone, Copy, PartialEq, Eq)]
struct StepPath {
    path: u64,
    depth: u8,
}

impl StepPath {
    /// The path to the subterm `join_walk` is at (`up`).
    fn of(up: &JoinPlace) -> StepPath {
        StepPath { path: up.iter().rev().fold(0, |p, e| p << 1 | e.3 as u64), depth: up.len() as u8 }
    }
    /// One level down (`depth > 0`): whether the path goes right, and the path from that child.
    fn down(self) -> (bool, StepPath) {
        (self.path & 1 == 1, StepPath { path: self.path >> 1, depth: self.depth - 1 })
    }
    /// After a step at this path, `join_walk`'s path in child `right`: None (skip it) for a child left of the path, and
    /// `Some(None)` for the rewritten subterm's children and those right of the path, which the walk takes whole.
    fn child(self, right: bool) -> Option<Option<StepPath>> {
        if self.depth == 0 {
            return Some(None);
        }
        let (on, next) = self.down();
        if on == right { Some(Some(next)) } else { right.then_some(None) }
    }
}

/// A join step from the reached term `from`: the step `table.join[eq]` at the subterm at `path`. The search keeps these
/// and makes plans only on the path that meets.
#[derive(Clone, Copy)]
struct JoinStep {
    from: Term,
    path: StepPath,
    eq: u32,
}

impl JoinStep {
    /// The step `eq` from `from` at the subterm `join_walk` is at (`up`).
    fn new(from: Term, up: &JoinPlace, eq: usize) -> JoinStep {
        JoinStep { from, path: StepPath::of(up), eq: eq as u32 }
    }
    /// The term the step reaches, its rewritten subterm `at` made.
    fn spine(self, at: Term) -> Spine {
        Spine { from: self.from, path: self.path, at }
    }
    /// The order of `join_walk` at `t`, the term the step reached: its path, unless the step shrank the term. A skipped
    /// step's other order passes a middle term of `size(t) - Δ + δ` (`Δ` this step's size change, `δ` the skipped one's)
    /// against the end term's `size(t) + δ`, so with `Δ >= 0` the cap stops neither and the search reaches the same terms
    /// (docs/tier-cycle.md, "Making the picks less sensitive").
    fn order(self, t: Term) -> Option<StepPath> {
        (t.size() >= self.from.size()).then_some(self.path)
    }
}

/// A term a join step reaches with its rewritten subterm made and the spine above it not: `from` with the subterm at
/// `path` replaced by `at`.
#[derive(Clone, Copy)]
struct Spine {
    from: Term,
    path: StepPath,
    at: Term,
}

impl Spine {
    /// One level down the path (`depth > 0`): the root's operator, its child off the path, whether the path goes right,
    /// and the spine from the child on it.
    fn down(self) -> (usize, Term, bool, Spine) {
        let Node::Op(o, a, b) = *self.from.node() else { unreachable!("a step's path stays in the term") };
        let (right, path) = self.path.down();
        (o, if right { a } else { b }, right, Spine { from: if right { b } else { a }, path, at: self.at })
    }
    fn make(self) -> Term {
        if self.path.depth == 0 {
            return self.at;
        }
        let (o, off, right, next) = self.down();
        let u = next.make();
        if right { Term::op(o, off, u) } else { Term::op(o, u, off) }
    }
    /// Whether `u` is this term: down `u` along the path, the children off it and then `at` compared by pointer.
    fn is(mut self, mut u: Term) -> bool {
        while self.path.depth > 0 {
            let (o, off, right, next) = self.down();
            match *u.node() {
                Node::Op(q, l, r) if q == o && (if right { l } else { r }) == off => u = if right { r } else { l },
                _ => return false,
            }
            self = next;
        }
        u == self.at
    }
    /// Whether this is `subst_pat(p, sub)`: down the pattern and the path together, then `is_subst` or `is` where one
    /// ends.
    fn is_pat(self, p: &Term, sub: &[Option<Term>]) -> bool {
        if self.path.depth == 0 {
            return is_subst(self.at, p, sub);
        }
        match *p.node() {
            Node::V(i) => sub[i].is_some_and(|t| self.is(t)),
            Node::Op(o, pa, pb) => {
                let (q, off, right, next) = self.down();
                o == q && if right { is_subst(off, &pa, sub) && next.is_pat(&pb, sub) } else { is_subst(off, &pb, sub) && next.is_pat(&pa, sub) }
            }
            _ => false,
        }
    }
    /// Whether this is the term at `up`'s root with the subterm at `up` replaced by `subst_pat(p, sub)`: down both paths
    /// while they agree; where they part, each side's child off its path against the other's; where one ends, `is_step`
    /// or `is_pat`.
    fn is_step(mut self, up: &JoinPlace, p: &Term, sub: &[Option<Term>]) -> bool {
        for (i, &(o, a, b, right)) in up.iter().enumerate() {
            if self.path.depth == 0 {
                return is_step(self.at, &up[i..], p, sub);
            }
            let (q, off, r, next) = self.down();
            let mine = if right { a } else { b };
            if o != q {
                return false;
            }
            if r != right {
                return next.is(mine) && is_step(off, &up[i + 1..], p, sub);
            }
            if off != mine {
                return false;
            }
            self = next;
        }
        self.is_pat(p, sub)
    }
}

/// Where `join_walk` is in a term: each ancestor of the subterm it is at, as its operator, children and whether the walk
/// went right.
type JoinPlace = [(usize, Term, Term, bool)];

/// `t`'s join steps of at most `cap` nodes in all, in order: those at the root by `table.join`, then those in the left
/// child, then the right; each passed to `visit` with its place, subterm, step index and match, while `visit` returns
/// true; a rule whose `Need` is over the cap, or that is `blocked` (being proved), is skipped unmatched. Adds the subterms it walks to `examined`.
/// After a step (`order`), only one order of two steps at disjoint places is walked: the subtrees left of the step's path
/// are skipped, as a step there and this one, the other taken first, reach the same term. `join_search` orders the walk
/// only after a step that did not shrink the term (`JoinStep::order`), where the cap cannot stop the other order's middle
/// term, so a search reaches the same terms at each depth as unordered: the same rules and M on salts 1-5, 6% less search
/// time (docs/tier-cycle.md, "The order made exact").
#[allow(clippy::too_many_arguments)]
fn join_walk(
    t: Term,
    order: Option<StepPath>,
    table: &RuleTable,
    blocked: &[RuleKey],
    cap: usize,
    up: &mut Vec<(usize, Term, Term, bool)>,
    examined: &mut Option<hashbrown::HashSet<Term>>,
    visit: &mut impl FnMut(&JoinPlace, Term, usize, &[Option<Term>; RULE_VARS], usize) -> bool,
) -> bool {
    crate::work::count(crate::work::Site::Walk);
    if let Some(x) = examined {
        x.insert(t);
    }
    let size = t.size();
    let room = cap as isize - size as isize;
    for (i, need) in table.join_index.get(&t) {
        if need.skips(room, cap as isize) {
            continue;
        }
        let e = &table.join[i];
        let mut sub = [None; RULE_VARS];
        if match_pat(&e.from, &t, &mut sub) && !blocked.iter().any(|&(l, r)| (l, r) == (e.lhs, e.rhs)) && !visit(up, t, i, &sub, cap) {
            return false;
        }
    }
    if let Node::Op(o, a, b) = *t.node() {
        for (right, c) in [(false, a), (true, b)] {
            let Some(order) = order.map_or(Some(None), |p| p.child(right)) else { continue };
            up.push((o, a, b, right));
            let go = join_walk(c, order, table, blocked, cap - (size - c.size()), up, examined, visit);
            up.pop();
            if !go {
                return false;
            }
        }
    }
    true
}

/// `(sh, size)` of `subst_pat(p, sub)`, without making it.
fn subst_sig(p: &Term, sub: &[Option<Term>]) -> (u64, usize) {
    match *p.node() {
        Node::V(i) => sub[i].map(|s| (s.sh(), s.size())).expect("bound"),
        Node::Op(o, a, b) => {
            let ((ha, za), (hb, zb)) = (subst_sig(&a, sub), subst_sig(&b, sub));
            (sh_op(o, ha, hb), 1 + za + zb)
        }
        _ => (p.sh(), 1),
    }
}

/// Whether `t` is `subst_pat(p, sub)`.
fn is_subst(t: Term, p: &Term, sub: &[Option<Term>]) -> bool {
    match (*p.node(), *t.node()) {
        (Node::V(i), _) => sub[i] == Some(t),
        (Node::Op(o, pa, pb), Node::Op(q, a, b)) => o == q && is_subst(a, &pa, sub) && is_subst(b, &pb, sub),
        (Node::Op(..), _) => false,
        _ => t == *p,
    }
}

/// The `sh` of the term at `up`'s root with the subterm at `up` replaced by one of `sh` `h`, without making it.
fn place_sh(up: &JoinPlace, h: u64) -> u64 {
    up.iter().rev().fold(h, |h, &(o, a, b, right)| if right { sh_op(o, a.sh(), h) } else { sh_op(o, h, b.sh()) })
}

/// Whether `t` is the term at `up`'s root with the subterm at `up` replaced by `subst_pat(p, sub)`.
fn is_step(mut t: Term, up: &JoinPlace, p: &Term, sub: &[Option<Term>]) -> bool {
    for &(o, a, b, right) in up {
        match *t.node() {
            Node::Op(q, l, r) if q == o && (if right { l == a } else { r == b }) => t = if right { r } else { l },
            _ => return false,
        }
    }
    is_subst(t, p, sub)
}

/// The plan of `step.from = ` the term the step reaches.
fn step_plan(job: &Job, step: &JoinStep) -> PlanRc {
    let (mut up, mut x, mut path) = (vec![], step.from, step.path);
    while path.depth > 0 {
        let Node::Op(o, a, b) = *x.node() else { unreachable!("a step's path stays in the term") };
        let right;
        (right, path) = path.down();
        up.push((o, a, b, right));
        x = if right { b } else { a };
    }
    let e = &job.rules().table.join[step.eq as usize];
    let mut sub = [None; RULE_VARS];
    assert!(match_pat(&e.from, &x, &mut sub), "a step's law matches where it was found");
    let law = Plan::law(job, e.kind, e.lhs, e.rhs, sub[..e.vars].iter().map(|s| s.unwrap_or(Term::v(0))).collect());
    let p = if e.backward { Plan::sym(job, law) } else { law };
    up.iter().rev().fold(p, |p, &(o, a, b, right)| if right { Plan::cong(job, o, Plan::refl(job, &a), p) } else { Plan::cong(job, o, p, Plan::refl(job, &b)) })
}

/// A term `join_search` reached: a side's own, or the step it was reached by with that step's rewritten subterm, the
/// spine above it made only when the search expands it or its path meets.
#[derive(Clone, Copy)]
enum Reached {
    Side(Term),
    Step(JoinStep, Term),
}

impl Reached {
    fn make(self) -> Term {
        match self {
            Reached::Side(t) => t,
            Reached::Step(step, at) => step.spine(at).make(),
        }
    }
    fn is(self, u: Term) -> bool {
        match self {
            Reached::Side(t) => t == u,
            Reached::Step(step, at) => step.spine(at).is(u),
        }
    }
    /// Whether this is the term at `up`'s root with the subterm at `up` replaced by `subst_pat(p, sub)`.
    fn is_step(self, up: &JoinPlace, p: &Term, sub: &[Option<Term>]) -> bool {
        match self {
            Reached::Side(t) => is_step(t, up, p, sub),
            Reached::Step(step, at) => step.spine(at).is_step(up, p, sub),
        }
    }
    fn step(self) -> Option<JoinStep> {
        match self {
            Reached::Side(_) => None,
            Reached::Step(step, _) => Some(step),
        }
    }
}

/// `join_eq`'s search, adding the terms it examined to `examined`. A step's term is looked up among those reached by its
/// `sh` and `is_step` before anything is made, so only new terms' rewritten subterms are made (58% of a cmp3d mine's steps
/// reached a term its side had: docs/tier-cycle.md, "Lazy join steps"); the spine above one is made only when the search
/// expands it or its path meets (36.8% of new terms were expanded: "What the join's duplicates and term building are"),
/// and plans only on the path that meets. With `feed`, a met path goes to the store the job feeds.
fn join_search(job: &mut Job, a: &Term, b: &Term, examined: &mut Option<hashbrown::HashSet<Term>>, feed: bool) -> Option<PlanRc> {
    let (cap, visit, t0) = (a.size().max(b.size()) + 2, join_visit(job), std::time::Instant::now());
    // each reached term by its `sh`
    type Seen = hashbrown::HashTable<(u64, Reached)>;
    let get = |seen: &Seen, t: Term| seen.find(t.sh(), |e| e.0 == t.sh() && e.1.is(t)).expect("reached").1.step();
    let path = |seen: &Seen, mut t: Term| -> PlanRc {
        let mut steps = vec![];
        while let Some(step) = get(seen, t) {
            steps.push(step_plan(job, &step));
            t = step.from;
        }
        steps.into_iter().rev().reduce(|a, b| Plan::trans(job, a, b)).unwrap_or_else(|| Plan::refl(job, &t))
    };
    let mut seen: [Seen; 2] = [Seen::new(), Seen::new()];
    for (side, t) in [(0, a), (1, b)] {
        seen[side].insert_unique(t.sh(), (t.sh(), Reached::Side(*t)), |e| e.0);
    }
    // each side's reached terms with their depth, and those not yet expanded by (depth plus size, index): least first, in
    // the order reached among equals
    let mut store = [vec![(Reached::Side(*a), 0)], vec![(Reached::Side(*b), 0)]];
    let mut pending: [BinaryHeap<Reverse<(usize, usize)>>; 2] = [BinaryHeap::from([Reverse((a.size(), 0))]), BinaryHeap::from([Reverse((b.size(), 0))])];
    let table = &*job.rules().table;
    let mut met_path: Vec<(Term, StoredStep)> = vec![];
    let found = (|| {
        let mut up = vec![];
        while !pending[0].is_empty() && !pending[1].is_empty() && seen[0].len() + seen[1].len() <= visit {
            let s = (pending[0].len() > pending[1].len()) as usize;
            let Reverse((_, i)) = pending[s].pop().expect("pending");
            let (r, depth) = store[s][i];
            let t = r.make();
            let mut met = None;
            let (here, there) = seen.split_at_mut(1);
            let (mine, other) = if s == 0 { (&mut here[0], &there[0]) } else { (&mut there[0], &here[0]) };
            let order = r.step().and_then(|s| s.order(t));
            join_walk(t, order, table, &job.blocked, cap, &mut up, examined, &mut |up, x, eq, sub, cap| {
                let e = &table.join[eq];
                let (h, size) = subst_sig(&e.to, sub);
                if size > cap || h == x.sh() && is_subst(x, &e.to, sub) {
                    return true;
                }
                let h = place_sh(up, h);
                let step = JoinStep::new(t, up, eq);
                if let Some(&(_, u)) = other.find(h, |c| c.0 == h && c.1.is_step(up, &e.to, sub)) {
                    met = Some((step, u));
                    return false;
                }
                if mine.find(h, |c| c.0 == h && c.1.is_step(up, &e.to, sub)).is_none() {
                    let r = Reached::Step(step, subst_pat(&e.to, sub));
                    mine.insert_unique(h, (h, r), |c| c.0);
                    pending[s].push(Reverse((depth + 1 + t.size() + size - x.size(), store[s].len())));
                    store[s].push((r, depth + 1));
                }
                true
            });
            let Some((step, u)) = met else { continue };
            let u = u.make();
            // the path's steps, for the store the job feeds
            if feed {
                let kept = |s: &JoinStep| {
                    let e = &table.join[s.eq as usize];
                    StoredStep { from: s.from, path: s.path, law: (e.lhs, e.rhs, e.backward) }
                };
                met_path.push((u, kept(&step)));
                for (side, mut p) in [(&seen[s], t), (&seen[1 - s], u)] {
                    while let Some(prev) = get(side, p) {
                        met_path.push((p, kept(&prev)));
                        p = prev.from;
                    }
                }
            }
            // a met search's result rests on its path only: keep what was examined at the path's terms
            if let Some(x) = examined {
                x.clear();
                let mut stack = vec![u];
                for (side, mut p) in [(&seen[s], t), (&seen[1 - s], u)] {
                    stack.push(p);
                    while let Some(prev) = get(side, p) {
                        p = prev.from;
                        stack.push(p);
                    }
                }
                // with their subterms
                while let Some(q) = stack.pop() {
                    if let (true, Node::Op(_, l, r)) = (x.insert(q), *q.node()) {
                        stack.extend([l, r]);
                    }
                }
            }
            // `this side = u` and `other side = u`
            let (here, there) = (Plan::trans(job, path(&seen[s], t), step_plan(job, &step)), path(&seen[1 - s], u));
            let (pa, pb) = if s == 0 { (here, there) } else { (there, here) };
            return Some(Plan::trans(job, pa, Plan::sym(job, pb)));
        }
        None
    })();
    let (reached, nanos) = ((seen[0].len() + seen[1].len()) as u64, t0.elapsed().as_nanos() as u64);
    if let Some(JoinStoreUse::Feed(st)) = job.join_store.as_mut() {
        for (to, step) in met_path {
            st.add(to, step);
        }
    }
    let c = &mut job.join_cost;
    (c.searches, c.reached, c.met, c.nanos) = (c.searches + 1, c.reached + reached, c.met + found.is_some() as u64, c.nanos + nanos);
    c.failed_nanos += if found.is_some() { 0 } else { nanos };
    found
}

/// `shr1 A = shr1 B` (or `0 = shr1 B`, as `shr1 0`) for machine-expressible `A`, `B`, without a lookahead machine: the
/// bit-0 mask law `shr1 t = shr1 (t & M)`, `M = shl1 -1`, turns the pair into the shift-free law `A & M = B & M`
/// (search note section 47).
pub fn shr_mask_eq(job: &mut Job, n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    let shr = |t: &Term| Term::op(SHR1, *t, Term::ZERO);
    let (mask, one_arg) = (Term::op(SHL1, Term::ONES, Term::ZERO), |t: &Term| match *t.node() {
        Node::Op(SHR1, x, _) if Machine::parse(&x).is_some() => Some(x),
        Node::Zero => Some(Term::ZERO),
        _ => None,
    });
    if job.setup().ablated("shrmask") || !matches!(*a.node(), Node::Op(SHR1, ..)) && !matches!(*b.node(), Node::Op(SHR1, ..)) {
        return None;
    }
    let (x, y) = (one_arg(a)?, one_arg(b)?);
    // the pair `A & M`, `B & M`: rewrite both, close with `prove_eq` (a machine law when they stay arithmetic)
    let (ta, tb) = (Term::op(AND, x, mask), Term::op(AND, y, mask));
    let ((r1, p1), (r2, p2)) = (rewrite(job, &ta, n, k), rewrite(job, &tb, n, k));
    let mid = prove_eq(job, n, k, &r1, &r2)?;
    let cong = Plan::cong(job, SHR1, Plan::trans(job, p1, Plan::trans(job, mid, Plan::sym(job, p2))), Plan::refl(job, &Term::ZERO));
    // `a = shr1 (A & M)` and `b = shr1 (B & M)`
    let mut side_proof = |orig: &Term, arg: &Term| -> Option<PlanRc> {
        if matches!(*orig.node(), Node::Zero) {
            // `0 = shr1 0 = shr1 (0 & M)`: the second step is a congruence on `0 = 0 & M` by the rewriter
            let (r, pr) = rewrite(job, &Term::op(AND, Term::ZERO, mask), n, k);
            if r != Term::ZERO {
                return None;
            }
            let (target, step) = rule_step(job, &shr(&Term::ZERO))?;
            if target != Term::ZERO {
                return None;
            }
            Some(Plan::trans(job, Plan::sym(job, step), Plan::cong(job, SHR1, Plan::sym(job, pr), Plan::refl(job, &Term::ZERO))))
        } else {
            Some(Plan::law(job, LawKind::Rule("shrmask"), shr(&Term::v(0)), shr(&Term::op(AND, Term::v(0), mask)), vec![*arg]))
        }
    };
    let (pa, pb) = (side_proof(a, &x)?, side_proof(b, &y)?);
    Some(Plan::trans(job, Plan::trans(job, pa, cong), Plan::sym(job, pb)))
}

/// The plan of `t1 = t2` over `k` variables: both sides rewritten, then closed with `prove_eq`; `None` when that cannot.
pub fn rewrite_plan(job: &mut Job, n: usize, k: usize, t1: &Term, t2: &Term) -> Option<PlanRc> {
    // an `lt` root (a one-bit result) is rewritten under its operands, then closed by congruence or, failing that,
    // by the `lt` machine proof for the rewritten pair; `lt` occurs only at the root
    let lt_roots = matches!((*t1.node(), *t2.node()), (Node::Op(LT, ..), Node::Op(LT, ..)));
    // each side gets the whole `RewriteState::budget`, so a side that cycles cannot leave the other half-normalized; afterwards the
    // budget is what the hungrier side left, so `job.rw.budget <= 0` still says some side used it up
    let budget0 = job.rw.budget;
    let ((r1, p1), left1) = (rewrite(job, t1, n, k), std::mem::replace(&mut job.rw.budget, budget0));
    let (r2, p2) = rewrite(job, t2, n, k);
    job.rw.budget = job.rw.budget.min(left1);
    let (p1, p2, mid) = if lt_roots {
        // `rewrite` normalizes the operands and applies the root rules; equal results close by `refl`, `lt` roots with
        // provable operands by congruence, the rest by the `lt` machine proof of the rewritten pair
        let mid = if r1 == r2 {
            Plan::refl(job, &r1)
        } else {
            let by_operands = if let (Node::Op(LT, a2, b2), Node::Op(LT, c2, d2)) = (*r1.node(), *r2.node()) {
                match (prove_eq(job, n, k, &a2, &c2), prove_eq(job, n, k, &b2, &d2)) {
                    (Some(pa), Some(pb)) => Some(Plan::cong(job, LT, pa, pb)),
                    _ => None,
                }
            } else {
                None
            };
            match by_operands {
                Some(plan) => plan,
                None => join_or_machine(job, n, k, &r1, &r2)?,
            }
        };
        (p1, p2, mid)
    } else {
        match prove_eq(job, n, k, &r1, &r2) {
            Some(mid) => (p1, p2, mid),
            // the rewriter may have pushed the shifts down to atoms; the mask reduction applies to the original sides
            None => (Plan::refl(job, t1), Plan::refl(job, t2), shr_mask_eq(job, n, k, t1, t2)?),
        }
    };
    Some(Plan::trans(job, Plan::trans(job, p1, mid), Plan::sym(job, p2)))
}

/// Proof of `t1 = t2` over `k` good vectors: `rewrite_plan`, compiled. `None` when there is no plan.
pub fn rewrite_law(job: &mut Job, n: usize, k: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    let plan = rewrite_plan(job, n, k, t1, t2)?;
    Some(law_proof(job, n, k, t1, t2, &plan))
}

/// The closed law `forall x.. gx... t1 = t2` proved by `plan`.
pub fn law_proof(job: &mut Job, n: usize, k: usize, t1: &Term, t2: &Term, plan: &Plan) -> (Expr, Expr) {
    let c = Compiler::new(n, k);
    let bv = bv_ty(n);
    let root = if matches!((*t1.node(), *t2.node()), (Node::Op(LT, ..), Node::Op(LT, ..))) { bv_ty(1) } else { bv };
    let (mut proof, mut stmt) = (c.proof(job, plan).2, id(root, c.ev(t1), c.ev(t2)));
    for _ in 0..k {
        let g = app(good_bv(n), var(k as u32 - 1));
        (proof, stmt) = (lam(g, proof), pi(g, stmt));
    }
    for _ in 0..k {
        (proof, stmt) = (lam(bv, proof), pi(bv, stmt));
    }
    (proof, stmt)
}

/// One law per kind of step (assoc and comm, a rule, a constant carry, the carry-encoding search, a collapse, an `lt` root, the
/// bit-0 mask): counting (`Rules::counting`) finds it too without building a plan, and the proving plan's sides are the law's and it
/// compiles to a proof the kernel accepts.
#[test]
fn plans_compile_to_checked_proofs() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let (v, z, ones) = (Term::v, Term::ZERO, Term::ONES);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let shr = |a: Term| op(SHR1, a, Term::ZERO);
        let laws = [
            (op(ADD, op(ADD, v(2), v(0)), v(1)), op(ADD, v(1), op(ADD, v(0), v(2)))),
            (op(SHL1, op(AND, v(0), v(1)), z), op(AND, op(SHL1, v(0), z), op(SHL1, v(1), z))),
            (op(ADD, v(0), op(XOR, v(0), ones)), ones),
            (op(SUB, ones, v(1)), op(XOR, v(1), ones)),
            (op(OR, v(0), op(AND, v(0), v(1))), v(0)),
            (op(LT, v(0), op(ADD, v(1), z)), op(LT, v(0), v(1))),
            (shr(op(ADD, v(0), v(0))), shr(op(SUB, op(ADD, v(0), v(0)), ones))),
        ];
        for (l, r) in &laws {
            let k = l.max_var().max(r.max_var()) + 1;
            let plans = [false, true].map(|counting| {
                let rules = job.rules().counting(counting);
                job.with_rules(rules, |job| rewrite_plan(job, 4, k, l, r)).unwrap_or_else(|| panic!("no plan for {} = {} (counting: {counting})", l.show(), r.show()))
            });
            assert!(matches!(*plans[1], Plan::Counting), "counting built a plan for {} = {}", l.show(), r.show());
            let (a, b, _) = Compiler::new(4, k).proof(job, &plans[0]);
            assert!((a, b) == (*l, *r), "{} = {}", l.show(), r.show());
            let (p, s) = law_proof(job, 4, k, l, r, &plans[0]);
            job.lemmas.ck(&format!("{} = {}", l.show(), r.show()), &p, &s);
        }
    })
}

/// The bounded join closes an equal pair by a mined rule and add commutativity (a plan whose sides are the pair's and which
/// the kernel accepts, and which counting finds too), and gives none for a pair that is not equal.
#[test]
fn join_eq_closes_an_equal_pair_by_rule_and_comm_steps() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let rules = job.rules().with_mined(job.setup(), vec![(parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"))]);
        job.with_rules(rules, |job| {
        let (n, k) = (4, 3);
        let (a, b) = (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)"));
        let counting = job.rules().counting(true);
        let counted = job.with_rules(counting, |job| join_eq(job, n, k, &a, &b));
        assert!(matches!(counted.as_deref(), Some(Plan::Counting)), "counting found no join");
        let plan = join_eq(job, n, k, &a, &b).expect("a join");
        assert!(Compiler::new(n, k).proof(job, &plan).0 == a && Compiler::new(n, k).proof(job, &plan).1 == b);
        let (p, s) = law_proof(job, n, k, &a, &b, &plan);
        job.lemmas.ck("joined", &p, &s);
        assert!(join_eq(job, n, k, &a, &parse_term("add(sub(add(x, y), -1), y)")).is_none());
        })
    })
}

/// A join step is known before it is made: `subst_sig` and `place_sh` give the `sh` and size of the term `subst_pat` and
/// `Spine::make` make, and `is_step` and `Spine::is_step` know that term from its place and match, against a made term or
/// a step's whose spine is not made, and only it.
#[test]
fn a_join_step_is_known_before_it_is_made() {
    let (x, z) = (Term::v(0), Term::v(2));
    let and = |a, b| Term::op(AND, a, b);
    let or = |a, b| Term::op(OR, a, b);
    let (p, inner) = (parse_term("add(sub(x, y), add(y, -1))"), parse_term("xor(and(z, x), 0)"));
    let mut sub = [None; RULE_VARS];
    (sub[0], sub[1]) = (Some(parse_term("add(y, z)")), Some(inner));
    let u = subst_pat(&p, &sub);
    assert!(subst_sig(&p, &sub) == (u.sh(), u.size()));
    // from `and(or(x, inner), z)`, left then right: `inner` becomes `u`
    let from = and(or(x, inner), z);
    let up = [(AND, or(x, inner), z, false), (OR, x, inner, true)];
    let step = JoinStep::new(from, &up, 0).spine(u);
    let t = step.make();
    assert!(t == and(or(x, u), z) && place_sh(&up, u.sh()) == t.sh());
    assert!(is_step(t, &up, &p, &sub) && step.is(t));
    for (other, why) in [(and(or(x, u), x), "another sibling"), (from, "another replacement"), (and(Term::op(XOR, x, u), z), "another operator")] {
        assert!(!is_step(other, &up, &p, &sub) && !step.is(other), "{why}");
    }
    // the same term by another step, neither spine made: at the same place
    assert!(step.is_step(&up, &p, &sub));
    assert!(!step.is_step(&[(AND, or(x, inner), x, false), (OR, x, inner, true)], &p, &sub), "another sibling");
    // at a place above the spine's end, its pattern down the spine
    let (q, mut sub2) = (parse_term("or(x, y)"), [None; RULE_VARS]);
    (sub2[0], sub2[1]) = (Some(x), Some(u));
    assert!(step.is_step(&[(AND, or(x, x), z, false)], &q, &sub2));
    assert!(!step.is_step(&[(AND, or(x, x), x, false)], &q, &sub2), "another sibling");
    let (r, mut sub3) = (parse_term("and(or(x, y), z)"), [None; RULE_VARS]);
    (sub3[0], sub3[1], sub3[2]) = (Some(x), Some(u), Some(z));
    assert!(step.is_step(&[], &r, &sub3));
    sub3[2] = Some(x);
    assert!(!step.is_step(&[], &r, &sub3), "another sibling under the pattern");
    // a pattern variable above the spine's end
    let (v, mut sub4) = (parse_term("and(y, z)"), [None; RULE_VARS]);
    (sub4[1], sub4[2]) = (Some(or(x, u)), Some(z));
    assert!(step.is_step(&[], &v, &sub4));
    sub4[1] = Some(or(x, inner));
    assert!(!step.is_step(&[], &v, &sub4), "another term for the variable");
    // at a place below the spine's end
    let mut other = sub;
    other[1] = Some(x);
    let shallow = JoinStep::new(from, &up[..1], 0).spine(or(x, u));
    assert!(shallow.make() == t && shallow.is(t) && shallow.is_step(&up, &p, &sub));
    assert!(!shallow.is_step(&up, &p, &other), "another match");
    // a pattern past the spine's end, and another operator under it
    sub3[2] = Some(z);
    assert!(shallow.is_step(&[], &r, &sub3) && !shallow.is_step(&[], &parse_term("and(xor(x, y), z)"), &sub3));
    sub3[1] = Some(x);
    assert!(!shallow.is_step(&[], &r, &sub3), "another term past the spine's end");
    // `and(u, or(x, u))` by a spine down the right child and a step down the left
    let right = JoinStep::new(and(u, z), &[(AND, u, z, true)], 0).spine(or(x, u));
    assert!(right.make() == and(u, or(x, u)) && right.is_step(&[(AND, z, or(x, u), false)], &p, &sub));
    assert!(!right.is_step(&[(AND, z, or(x, x), false)], &p, &sub), "paths apart, another sibling");
    assert!(!right.is_step(&[(AND, z, or(x, u), false)], &p, &other), "paths apart, another match");
    // a pattern at the root down a spine that goes right, and another operator at the root
    let (w, mut sub5) = (parse_term("and(x, y)"), [None; RULE_VARS]);
    (sub5[0], sub5[1]) = (Some(u), Some(or(x, u)));
    assert!(right.is_step(&[], &w, &sub5) && !right.is_step(&[], &parse_term("xor(x, y)"), &sub5));
    sub5[0] = Some(z);
    assert!(!right.is_step(&[], &w, &sub5), "another term off the right");
    (sub5[0], sub5[1]) = (Some(u), Some(or(x, x)));
    assert!(!right.is_step(&[], &w, &sub5), "another term down the right");
}

#[test]
pub fn laws_over_three_vectors_check_and_false_ones_fail() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        for n in [1usize, 3] {
            // bitwise (x ^ y) ^ z = x ^ (y ^ z)
            let (p, s) = bitwise_law_k(n, 3, &op(3, op(3, v(0), v(1)), v(2)), &op(3, v(0), op(3, v(1), v(2))));
            job.lemmas.ck(&format!("xor assoc at n={n}"), &p, &s);
            assert!(job.lemmas.holds(&bitwise_law_k(n, 3, &op(1, v(0), v(2)), &op(2, v(0), v(2))).0, &bitwise_law_k(n, 3, &op(1, v(0), v(2)), &op(2, v(0), v(2))).1).is_err());
            // add associativity over three vectors, and a non-law
            let (p, s) = rewrite_law(job, n, 3, &op(0, op(0, v(0), v(1)), v(2)), &op(0, v(0), op(0, v(1), v(2)))).expect("assoc");
            job.lemmas.ck(&format!("add assoc at n={n}"), &p, &s);
            let (p, s) = rewrite_law(job, n, 3, &op(0, op(0, v(2), v(0)), v(1)), &op(0, v(1), op(0, v(0), v(2)))).expect("comm+assoc");
            job.lemmas.ck(&format!("add comm assoc at n={n}"), &p, &s);
            assert!(rewrite_law(job, n, 3, &op(0, v(0), v(2)), &op(0, v(0), v(1))).is_none());
        }
    })
}

#[test]
pub fn rewrite_law_proves_add_conjectures_from_the_library_lemmas() {
    let job = &mut Job::new(Setup::process());
    let v = |i: usize| Term::v(i);
    let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
    let n = 4;
    for (name, t1, t2) in [
        ("or (add x 0) y = or y x", op(2, op(0, v(0), Term::ZERO), v(1)), op(2, v(1), v(0))),
        ("xor (add x y) y = xor y (add y x)", op(3, op(0, v(0), v(1)), v(1)), op(3, v(1), op(0, v(1), v(0)))),
        ("add (and x y) y = add y (and y x)", op(0, op(1, v(0), v(1)), v(1)), op(0, v(1), op(1, v(1), v(0)))),
    ] {
        let (p, s) = rewrite_law(job, n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no rewrite proof"));
        job.lemmas.ck(name, &p, &s);
    }
    // associativity instances, including one that needs reordering as well
    for (name, t1, t2) in [
        ("add (add x y) y = add x (add y y)", op(0, op(0, v(0), v(1)), v(1)), op(0, v(0), op(0, v(1), v(1)))),
        ("add (add y y) x = add (add x y) y", op(0, op(0, v(1), v(1)), v(0)), op(0, op(0, v(0), v(1)), v(1))),
    ] {
        let (p, s) = rewrite_law(job, n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no rewrite proof"));
        job.lemmas.ck(name, &p, &s);
    }
    // a false law is refused by the truth-table pre-check
    assert!(rewrite_law(job, n, 2, &op(0, v(0), v(1)), &op(0, v(0), v(0))).is_none());
}

#[test]
pub fn a_law_over_lemma_parameters_discharges_to_a_closed_proof() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let (p, s) = rewrite_law(job, 2, 3, &op(0, op(0, v(2), v(0)), v(1)), &op(0, v(1), op(0, v(0), v(2)))).expect("comm+assoc");
        assert!(job.lemmas.params.as_ref().is_some_and(|(.., b)| !b.is_empty()), "no lemma was bound");
        assert!(check(&Ctx::new(), &p, &s).is_err(), "a proof over lemma parameters is not closed");
        job.lemmas.ck("over parameters", &p, &s);
        // a machine proof's case lemmas are parameters too
        let add = |a: Term, b: Term| op(0, a, b);
        let (pm, sm) = add_tree_law(job, 2, 3, &add(add(v(0), v(1)), v(2)), &add(v(0), add(v(1), v(2)))).expect("assoc3");
        assert!(check(&Ctx::new(), &pm, &sm).is_err(), "the machine proof's lemmas are not parameters");
        job.lemmas.ck("machine over parameters", &pm, &sm);
        // a lemma whose proof uses lemmas bound before it: a rule proved through a machine proof
        let scopes = |job: &Job| job.lemmas.params.as_ref().map_or(0, |(_, b)| b.len());
        let before = scopes(job);
        let (l, r) = (add(op(4, v(0), v(1)), v(2)), add(op(4, v(2), v(1)), v(0)));
        let (pr, sr) = shared_lemma(job, "nested".into(), |job| prove_rule(job, 2, 3, &l, &r).expect("rule"));
        assert!(scopes(job) >= before + 2, "the rule's proof bound no lemma of its own");
        let all = apps(lam(sm, lam(shift(&s, 0, 1), lam(shift(&sr, 0, 2), var(2)))), vec![pm, p, pr]);
        ck("discharged", &discharge(job, all), &sm);
    })
}

#[test]
pub fn a_second_discharge_in_a_job_applies_only_the_lemmas_bound_after_the_first() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let lemma = |n: usize| (good_lit(n, 0), app(good_bv(n), lit(n, 0)));
        let (ra, sa) = shared_lemma(job, "A".into(), |_| lemma(2));
        ck("A", &discharge(job, ra), &sa);
        let (rb, sb) = shared_lemma(job, "B".into(), |_| lemma(3));
        assert!(discharge(job, rb) == app(lam(sb, var(0)), lemma(3).0), "the second discharge applies B's proof alone");
        // A asked for again after a discharge is bound afresh, not the ended scope's parameter
        let (ra, _) = shared_lemma(job, "A".into(), |_| lemma(2));
        ck("A again", &discharge(job, ra), &sa);
    })
}

// ---- Carry-chain builder (search note section 13): `add A B = T` for bitwise A, B, T over x, y, with no
// lemma-specific template. It *discovers* the proof invariant: a constant value R for the carry that is
// inductive (the carry stays R for every pair of operand bits, starting from the initial `false`) and under
// which every sum bit equals the target bit. Both are decided by truth table before anything is built.

/// The constant carry value (as a literal bit) that works for `add a b = t`, if any.
pub fn find_constant_carry(a: &Term, b: &Term, t: &Term) -> Option<bool> {
    [false, true].into_iter().find(|&r| {
        // the initial carry is `false`, so only `false` can be maintained from the start
        !r && (0..4).all(|m| {
            let bits = [m & 1 == 1, m & 2 == 2];
            let [ab, bb, tb] = [a, b, t].map(|x| term_gb(&Bools, x, &bits));
            Bools.maj(&ab, &bb, &r) == r && Bools.sum3(&ab, &bb, &r) == tb
        })
    })
}

/// Proof of `t1 = t2` where `t1 = add A B` (bitwise `A`, `B`) and `t2` is bitwise, over two good vectors, by the
/// discovered constant-carry invariant; `None` when no constant carry works.
pub fn carry_chain_law(n: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    let Node::Op(ADD, a_term, b_term) = *t1.node() else { return None };
    if a_term.uses_add() || b_term.uses_add() || t2.uses_add() || t1.max_var().max(t2.max_var()) > 1 {
        return None;
    }
    let r = bit(find_constant_carry(&a_term, &b_term, t2)?);
    let carry = |x: Expr, y: Expr, c: Expr| or(and(x, y), and(c, xor(x, y)));
    // per-bit lemmas, by case analysis on the two operand bits
    let (p_carry, _) = lemma2(
        &|x, y| id(bool0(), carry(a_term.bit(&[x, y]), b_term.bit(&[x, y]), r), r),
        &|_, _| refl(r),
    );
    let (p_sum, _) = lemma2(
        &|x, y| id(bool0(), sum3(a_term.bit(&[x, y]), b_term.bit(&[x, y]), r), t2.bit(&[x, y])),
        &|vx, vy| refl(t2.bit(&[bit(vx), bit(vy)])),
    );
    Some(two_var_law(n, t1, t2, &|a, ga, b, gb| {
        let bl = bool0();
        let (ai, bi) = (|i: usize| a_term.bit(&[a(i), b(i)]), |i: usize| b_term.bit(&[a(i), b(i)]));
        let mut c = vec![r];
        let mut pc: Vec<Option<Expr>> = vec![None];
        let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
        for i in 0..n {
            let args = vec![a(i), b(i), ga(i), gb(i)];
            // sum bit: rewrite the carry to R, then the sum lemma
            let s_i = sum3(ai(i), bi(i), c[i]);
            let to_target = apps(p_sum, args.clone());
            e.push(match &pc[i] {
                None => to_target,
                Some(pci) => {
                    let fmap = lam(bl, sum3(shift(&ai(i), 0, 1), shift(&bi(i), 0, 1), var(0)));
                    let rewritten = cong1(&bl, &bl, &fmap, c[i], r, *pci);
                    trans_proof(&bl, &s_i, &sum3(ai(i), bi(i), r), &t2.bit(&[a(i), b(i)]), rewritten, to_target)
                }
            });
            s1.push(s_i);
            s2.push(t2.bit(&[a(i), b(i)]));
            // next carry stays R
            let next = carry(ai(i), bi(i), c[i]);
            let stays = apps(p_carry, args);
            pc.push(Some(match &pc[i] {
                None => stays,
                Some(pci) => {
                    let fmap = lam(bl, carry(shift(&ai(i), 0, 1), shift(&bi(i), 0, 1), var(0)));
                    let rewritten = cong1(&bl, &bl, &fmap, c[i], r, *pci);
                    trans_proof(&bl, &next, &carry(ai(i), bi(i), r), &r, rewritten, stays)
                }
            }));
            c.push(next);
        }
        (s1, s2, e)
    }))
}

#[test]
pub fn carry_chain_builder_finds_the_constant_carry() {
    let v = |i: usize| Term::v(i);
    let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
    for n in [1usize, 2, 4] {
        for (name, t1, t2) in [
            ("add x (xor x -1) = -1", op(0, v(0), op(3, v(0), Term::ONES)), Term::ONES),
            ("add (xor -1 y) y = -1", op(0, op(3, Term::ONES, v(1)), v(1)), Term::ONES),
            ("add x 0 = x", op(0, v(0), Term::ZERO), v(0)),
            ("add (and x 0) y = y", op(0, op(1, v(0), Term::ZERO), v(1)), v(1)),
        ] {
            let (p, s) = carry_chain_law(n, &t1, &t2).unwrap_or_else(|| panic!("{name}: no constant carry"));
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        // no constant carry exists for these
        assert!(carry_chain_law(n, &op(0, v(0), v(1)), &op(0, v(1), v(0))).is_none());
        assert!(carry_chain_law(n, &op(0, v(0), Term::ONES), &v(0)).is_none());
    }
}

// ---- Searching for the carry-state encoding (search note sections 14 and 15). A sum tree of `c + 1` leaves (each
// leaf an add-free bitwise term over `k` vectors) is a ripple machine with `c` carries, one per `add` node. Two
// such sums agree if some encoding phi = (phi_1..phi_m) of the carry vector (m Boolean functions of the `c`
// carries) carries enough information: each side's output bit and next phi-values must be functions of (the `k`
// operand bits, phi(carries)), the same functions on both sides. `moore_encoding` computes the coarsest one by partition
// refinement; the proof is the associativity proof with the discovered phi in
// place of the hand-derived (xor, and) -- for a three-leaf sum, the total carry in binary.

/// A rule proved inside a rewrite (`proving`) runs with its rule blocked and as a rewriting job of its own: the caller's
/// budget, trace, fallbacks and blocked rules are as before.
#[test]
fn proving_leaves_the_callers_rewrite_state() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        (job.rw.budget, job.rw.trace, job.rw.fallbacks) = (777, Some(vec![]), 5);
        let blocked = job.blocked.len();
        let (l, r) = (parse_term("shr1(xor(x, -1), 0)"), parse_term("xor(shr1(x, 0), shr1(-1, 0))"));
        let inner = proving(job, &[(l, r)], |job| {
            let blocked = job.blocked.len();
            (blocked, rewrite_law(job, 4, 1, &l, &r).is_some())
        });
        assert_eq!(inner, (blocked + 1, true));
        assert_eq!((job.rw.budget, job.rw.trace.as_ref().map(Vec::len), job.rw.fallbacks, job.blocked.len()), (777, Some(0), 5, blocked));
    })
}

/// sbo3's rewrite cycle (docs/tier-cycle.md, "Why ordered sbo3 still cycled"): two rules and a permutative one bring
/// `sub(sub(z, x), sub(y, z))` back to itself. `rewrite` cuts it, so the law is proved without using up the step budget, and the
/// proof checks.
/// The table's normal form is off: this tests the rules' cuts and memo, which act only where the table does not (spec,
/// Testing).
#[test]
fn rewrite_cycles_are_cut() {
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));
    tatic::kernel::scoped(|| {
        let rules = "sub(sub(x, y), z) -> sub(x, add(y, z))\nadd(x, sub(y, z)) -> sub(x, sub(z, y))\nsub(x, sub(y, z)) -> sub(z, sub(y, x))\n";
        let (t1, t2) = (parse_term("sub(sub(z, x), sub(y, z))"), parse_term("sub(add(z, z), add(x, y))"));
        let (out, spent) = job.measured(LAW_STEPS, |job| job.with_mined(parse_rules(rules), |job| rewrite_law(job, 4, 3, &t1, &t2)));
        let (cuts, left) = (spent.cycle_cuts, LAW_STEPS - spent.steps);
        println!("cuts {cuts}, budget left {left}, proved {}", out.is_some());
        assert!(cuts > 0, "no cycle cut");
        assert!(left > 0, "the step budget ran out");
        let (p, s) = out.expect("proved");
        job.lemmas.ck("cycle law", &p, &s);
    })
}

/// cmp3d's growing chain (docs/tier-cycle.md, "Growth cut"): the two rules rewrite into each other and each lap copies the first
/// argument in, so no term repeats. The term on the path embeds in its larger copy, and the cut ends the chain there instead of at
/// the budget (which it runs out with only the repeat cut).
/// The table's normal form is off: this tests the rules' cuts and memo, which act only where the table does not (spec,
/// Testing).
#[test]
fn growing_rewrite_chains_are_cut() {
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));
    tatic::kernel::scoped(|| {
        let rules = "lt(x, sub(y, z)) -> lt(x, add(sub(x, y), z))\nlt(x, add(y, z)) -> lt(x, sub(sub(x, y), z))\n";
        let (t1, t2) = (parse_term("lt(z, add(add(x, x), y))"), parse_term("lt(z, add(y, add(x, x)))"));
        let (out, spent) = job.measured(LAW_STEPS, |job| job.with_mined(parse_rules(rules), |job| rewrite_law(job, 4, 3, &t1, &t2)));
        let (cuts, left) = (spent.cycle_cuts, LAW_STEPS - spent.steps);
        println!("cuts {cuts}, budget left {left}, proved {}", out.is_some());
        assert!(cuts > 0, "no growth cut");
        assert!(left > 0, "the step budget ran out");
        if let Some((p, s)) = out {
            job.lemmas.ck("growth law", &p, &s);
        }
    })
}

/// `RewriteMemo::filtered`: a memo built under some rules keeps its results under one more rule, tried last, for the entries whose
/// traces that rule's left side matches at no term where no rule fired; the rule miner seeds each candidate's scoring with them. The whole memo would replay
/// results the extra rule changes.
/// A pattern matches a term only where the term's shape has every bit the pattern needs, so a trace whose shapes lack one
/// can be skipped (docs/tier-cycle.md, "Survey: the next lever"); and the filter does reject.
#[test]
fn shapes_hold_every_bit_a_matching_pattern_needs() {
    let rules = parse_rules("sub(sub(x, y), z) -> sub(x, add(y, z))\nor(x, and(x, y)) -> x\nadd(x, 0) -> x\nxor(x, x) -> 0\nand(-1, x) -> x\nx -> x\n");
    let mut subs = vec![];
    for t in ["sub(sub(add(x, y), z), sub(x, 0))", "or(and(x, y), and(x, and(x, y)))", "xor(add(x, 0), add(x, 0))", "and(-1, -1)", "sub(x, add(y, z))"] {
        parse_term(t).subterms(&mut subs);
    }
    let mut matched = 0;
    for (l, _) in &rules {
        for t in &subs {
            if matches(l, t) {
                matched += 1;
                assert_eq!(t.shape() & l.needs(), l.needs(), "{} matches {} but its shape lacks a needed bit", l.show(), t.show());
            }
        }
    }
    assert!(matched > rules.len(), "every rule matches somewhere");
    let (l, t) = (parse_term("and(x, or(y, z))"), parse_term("and(x, y)"));
    assert_ne!(t.shape() & l.needs(), l.needs(), "an or child is needed and missing");
}

/// The table's normal form is off: this tests the rules' cuts and memo, which act only where the table does not (spec,
/// Testing).
#[test]
fn filtered_memo_entries_hold_under_an_extra_rule() {
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));
    let (n, kv) = (4, 3);
    let terms: Vec<Term> =
        ["sub(sub(z, x), sub(y, z))", "add(sub(x, y), sub(add(y, z), x))", "sub(add(x, y), sub(z, x))", "or(sub(x, y), and(sub(x, y), z))"].iter().map(|s| parse_term(s)).collect();
    let base = parse_rules("sub(add(x, y), z) -> add(sub(x, z), y)\n");
    // every term rewritten under `rules` with `memo` in force: the normal forms, the steps used, and the memo afterwards
    let run = |job: &mut Job, rules: &[(Term, Term)], memo: RewriteMemo| {
        job.rw.memo = Some(memo);
        job.rw.trace = Some(vec![]);
        let out: Vec<(String, i64)> = job.with_mined(rules.to_vec(), |job| {
            terms
                .iter()
                .map(|t| {
                    let (nf, spent) = job.measured(LAW_STEPS, |job| rewrite(job, t, n, kv).0.show());
                    (nf, spent.steps)
                })
                .collect()
        });
        job.rw.trace = None;
        (out, job.rw.memo.take().unwrap())
    };
    let (before, memo) = run(job, &base, RewriteMemo::new(kv));
    for extra in ["sub(sub(x, y), z) -> sub(x, add(y, z))\n", "or(x, and(x, y)) -> x\n"] {
        let rules: Vec<(Term, Term)> = base.iter().cloned().chain(parse_rules(extra)).collect();
        let l = &rules.last().unwrap().0;
        let seed = memo.filtered(|tr| !tr.touched_by(rules.last().unwrap(), |fired| fired.preempted_by(|f| run_order(l, &rules.last().unwrap().1) < run_order(&f.0, &f.1))));
        assert!(!seed.map.is_empty() && seed.map.len() < memo.map.len(), "{extra}: the filter kept {} of {}", seed.map.len(), memo.map.len());
        let fresh = run(job, &rules, RewriteMemo::new(kv)).0;
        assert_eq!(run(job, &rules, seed).0, fresh, "{extra}");
        // the unfiltered memo would replay `before` (debug builds reject such a replay, `check_replay`)
        assert_ne!(before, fresh, "{extra}: the extra rule changes nothing here");
    }
}

/// The join's trace under `rules`: the terms `join_eq` recorded (`Fired::Join`) and whether it met.
fn join_trace(job: &mut Job, a: &str, b: &str, rules: &str) -> (bool, Trace) {
    job.rw.trace = Some(vec![]);
    let met = job.with_mined(parse_rules(rules), |job| join_eq(job, 4, 3, &parse_term(a), &parse_term(b)).is_some());
    (met, Trace::new(job.rw.trace.take().unwrap()))
}

/// A join that fails records every term it examined (`Fired::Join`), so a candidate that could make it meet is seen: in the
/// join a rule acts wherever either usable side matches, here at a term no rewrite of the two sides asks about.
#[test]
fn failed_join_traces_every_term_it_examines() {
    let job = &mut Job::new(Setup::process());
    let (a, b) = ("sub(x, y)", "sub(0, sub(y, x))");
    let (met, joined) = join_trace(job, a, b, "");
    assert!(!met);
    // ~(y - x) = x - y - 1, at `xor(sub(y, x), -1)`, a step from `sub(0, sub(y, x))`
    let rule = parse_rules("xor(sub(x, y), -1) -> add(sub(y, x), -1)\n")[0];
    let sides = Trace::new(vec![(parse_term(a), Fired::None), (parse_term(b), Fired::None)]);
    assert!(!sides.touched_by(&rule, |_| true), "the rule's left side matches neither side");
    assert!(joined.touched_by(&rule, |_| true), "the join examined a term the rule's left side matches");
    let back = (parse_term("and(x, or(y, x))"), rule.0);
    assert!(joined.touched_by(&back, |_| true), "a rule whose right side matches there acts backward");
    assert!(!Trace::new(joined.items().iter().map(|(t, _)| (*t, Fired::None)).collect()).touched_by(&back, |_| true), "but not in a rewrite");
    assert!(!joined.touched_by(&parse_rules("or(x, and(x, y)) -> x\n")[0], |_| true), "no or anywhere, and x cannot be a step's start");
}

/// A join that meets records only the terms on its path (what the search examined at them), where the rules its plan used
/// fired: a rule added elsewhere leaves the plan a proof (the miner's error is a search that more rules would push past the
/// visit cap, docs/decisions/2026-10-17-monotone-join.md), and a rule it used, removed, touches the trace.
#[test]
fn met_join_traces_its_path_only() {
    let job = &mut Job::new(Setup::process());
    let (a, b) = ("add(add(z, y), sub(x, -1))", "add(sub(add(x, y), -1), z)");
    let (met, joined) = join_trace(job, a, b, "");
    assert!(met);
    for t in [a, b] {
        assert!(joined.items().iter().any(|(u, _)| *u == parse_term(t)), "{t} is on the path");
    }
    // -(~x) = x + 1, at `sub(0, xor(x, -1))`, a term the search examined off its path
    assert!(!joined.touched_by(&parse_rules("sub(0, xor(x, -1)) -> sub(0, sub(-1, x))\n")[0], |_| true));
    let rule = "or(x, y) -> add(xor(x, y), and(x, y))\n";
    let (met, joined) = join_trace(job, "or(x, y)", "add(xor(x, y), and(x, y))", rule);
    assert!(met);
    assert!(joined.touched_by(&parse_rules(rule)[0], |_| true), "the plan used the rule");
}

/// `TraceIndex::touched` gives the traces `Trace::touched_by` accepts, for rules matching forward, backward and nowhere, and
/// for a condition on the fired rule.
/// The table's normal form is off: this tests the rules' cuts and memo, which act only where the table does not (spec,
/// Testing).
#[test]
fn trace_index_agrees_with_touched_by() {
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));
    let (n, kv) = (4, 3);
    let mut traces: Vec<Trace> = [("sub(x, y)", "sub(0, sub(y, x))"), ("add(add(z, y), sub(x, -1))", "add(sub(add(x, y), -1), z)"), ("xor(xor(x, y), z)", "xor(z, xor(y, x))")]
        .iter()
        .map(|(a, b)| join_trace(job, a, b, "").1)
        .collect();
    for t in ["sub(sub(x, y), and(x, y))", "or(and(x, y), xor(x, -1))", "add(x, sub(0, x))", "xor(or(x, y), and(x, y))"] {
        job.rw.trace = Some(vec![]);
        rewrite(job, &parse_term(t), n, kv);
        traces.push(Trace::new(job.rw.trace.take().unwrap()));
    }
    traces.push(Trace::default());
    let index = TraceIndex::new(&traces);
    // rules whose sides are the traces' own terms (each matches itself) and patterns with variables
    let mut terms: Vec<Term> = traces.iter().flat_map(|tr| tr.items().iter().map(|(t, _)| *t)).collect();
    terms.sort();
    terms.dedup();
    let mut rules: Vec<(Term, Term)> = terms.iter().step_by(7).zip(terms.iter().skip(3).step_by(11)).map(|(l, r)| (*l, *r)).collect();
    rules.extend(parse_rules("xor(sub(x, y), -1) -> add(sub(y, x), -1)\nor(x, and(x, y)) -> x\nsub(x, y) -> add(x, sub(0, y))\nadd(x, y) -> add(y, x)\n"));
    rules.push((parse_term("and(x, or(y, x))"), parse_term("xor(sub(x, y), -1)")));
    rules.extend(parse_rules("and(and(and(x, y), z), and(x, y)) -> and(x, and(y, z))\nor(or(x, -1), or(y, -1)) -> -1\n"));
    let (mut some, mut none, mut narrowed) = (0, 0, 0);
    for rule in &rules {
        let mut got = vec![];
        for also in [&(|_: &Fired| true) as &dyn Fn(&Fired) -> bool, &|f: &Fired| *f != Fired::Fixed, &|f: &Fired| *f == Fired::Join] {
            let want: Vec<usize> = (0..traces.len()).filter(|&i| traces[i].touched_by(rule, also)).collect();
            assert_eq!(index.touched(rule, also), want, "{} -> {}", rule.0.show(), rule.1.show());
            if want.is_empty() { none += 1 } else { some += 1 }
            got.push(want);
        }
        narrowed += (got[0] != got[2]) as usize;
    }
    assert!(some > 20 && none > 5 && narrowed > 3, "touched {some}, untouched {none}, narrowed by the condition {narrowed}");
}

/// Join results are kept in `RewriteMemo` with the terms each search examined: under an extra rule `filtered` keeps the entries
/// the rule touches nowhere, and they give what a fresh search would; a hit gives the stored result.
#[test]
fn filtered_join_entries_hold_under_an_extra_rule() {
    let job = &mut Job::new(Setup::process());
    let (n, kv) = (4, 3);
    let pairs: Vec<(Term, Term)> = [("or(x, y)", "add(xor(x, y), and(x, y))"), ("xor(xor(x, y), z)", "xor(z, xor(y, x))")]
        .iter()
        .map(|(a, b)| (parse_term(a), parse_term(b)))
        .collect();
    let run = |job: &mut Job, rules: Vec<(Term, Term)>, memo: RewriteMemo| {
        job.rw.memo = Some(memo);
        let out: Vec<bool> = job.with_mined(rules, |job| pairs.iter().map(|(a, b)| join_eq(job, n, kv, a, b).is_some()).collect());
        (out, job.rw.memo.take().unwrap())
    };
    let (before, memo) = run(job, vec![], RewriteMemo::new(kv));
    assert_eq!(memo.joins.len(), pairs.len());
    assert_eq!(run(job, vec![], memo.filtered(|_| true)).0, before, "hits");
    let rule = parse_rules("or(x, y) -> add(xor(x, y), and(x, y))\n")[0];
    let seed = memo.filtered(|tr| !tr.touched_by(&rule, |_| true));
    assert_eq!(seed.joins.len(), 1, "the xor pair's search met no or, nor xor beside and under add");
    let fresh = run(job, vec![rule], RewriteMemo::new(kv)).0;
    assert_eq!(run(job, vec![rule], seed).0, fresh);
    assert_ne!(before, fresh, "the rule joins the first pair");
}

/// `Job::join_cost` counts the searches run, the terms they reached and the ones that met; a memo hit runs none and counts as a hit.
#[test]
fn join_cost_counts_searches_but_not_memo_hits() {
    let job = &mut Job::new(Setup::process());
    let (a, b) = (parse_term("xor(xor(x, y), z)"), parse_term("xor(z, xor(y, x))"));
    job.rw.memo = Some(RewriteMemo::new(3));
    let (first, s1) = job.spent(|job| join_eq(job, 4, 3, &a, &b).is_some());
    let (second, s2) = job.spent(|job| join_eq(job, 4, 3, &a, &b).is_some());
    job.rw.memo.take();
    assert!(first && second);
    assert_eq!((s1.join.searches, s1.join.met), (1, 1));
    assert!(s1.join.reached >= 2, "both sides at least");
    assert_eq!(s2.join, JoinCost { hits: 1, ..JoinCost::default() }, "the second call was a hit");
    assert!(s1.join.nanos > 0 && s1.join.failed_nanos == 0, "a met search's time counts, not as failed");
    // an equal pair the join cannot close (`failed_join_traces_every_term_it_examines`)
    let (closed, s3) = job.spent(|job| join_eq(job, 4, 3, &parse_term("sub(x, y)"), &parse_term("sub(0, sub(y, x))")).is_some());
    assert!(!closed && s3.join.met == 0 && s3.join.failed_nanos > 0 && s3.join.nanos == s3.join.failed_nanos);
}

/// The join store serves a pair it holds a path for, with a plan the kernel accepts (and by counting, `Rules::counting`),
/// without a search; it serves none once a law on the path leaves the table, and no job without a store is served.
#[test]
fn join_store_serves_a_stored_path_under_its_laws_only() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let rule = (parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"));
        let (n, k) = (4, 3);
        let (a, b) = (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)"));
        let join = |job: &mut Job| {
            job.rw.memo = Some(RewriteMemo::new(k));
            let (plan, spent) = job.spent(|job| join_eq(job, n, k, &a, &b));
            job.rw.memo.take();
            (plan, spent.join.searches, spent.join.stored)
        };
        job.with_mined(vec![rule], |job| {
            assert!(matches!(join(job), (Some(_), 1, 0)), "no store: searched");
            job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
            assert!(matches!(join(job), (Some(_), 1, 0)), "an empty store: searched, and the path fed");
            let (plan, searches, stored) = join(job);
            assert_eq!((searches, stored), (0, 1), "served from the store");
            let plan = plan.expect("a stored join");
            assert!(Compiler::new(n, k).proof(job, &plan).0 == a && Compiler::new(n, k).proof(job, &plan).1 == b);
            let (p, s) = law_proof(job, n, k, &a, &b, &plan);
            job.lemmas.ck("stored", &p, &s);
            let counting = job.rules().counting(true);
            let (counted, _, stored) = job.with_rules(counting, |job| join(job));
            assert!(matches!(counted.as_deref(), Some(Plan::Counting)) && stored == 1, "counting is served too");
        });
        assert_eq!(join(job).2, 0, "the rule left: no stored path");
        job.join_store = None;
    })
}

/// A cached failed search stands only while the join store has no path for its pair: the store grows as searches feed it,
/// and a failure cached before (in a seeded memo, `RewriteMemo::filtered`) hid a path the miner's scoring workers saw, so a
/// mine re-chose a rule it had for each round's phantom gain (run 2026-10-22-hidden-twins-2, 8631 rounds).
#[test]
fn a_cached_failed_join_yields_to_a_stored_path() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let (n, k) = (4, 3);
        let rule = (parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"));
        let (a, b) = (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)"));
        job.with_mined(vec![rule], |job| {
            job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
            job.rw.memo = Some(RewriteMemo::new(k));
            assert!(join_eq(job, n, k, &a, &b).is_some(), "searched, and the path fed");
            let mut stale = RewriteMemo::new(k);
            stale.joins.insert((a, b), std::rc::Rc::new((None, Trace::default())));
            job.rw.memo = Some(stale);
            let (plan, spent) = job.spent(|job| join_eq(job, n, k, &a, &b));
            assert!(plan.is_some() && spent.join.stored == 1, "served from the store over the cached failure");
            assert!(job.rw.memo.take().unwrap().joins[&(a, b)].0.is_some(), "the memo now holds the met join");
            job.join_store = None;
        })
    })
}

/// A worker reads the store as it was frozen: what the feeding job adds later is not in its copy.
#[test]
fn join_store_workers_read_the_frozen_copy() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let k = 3;
        job.with_mined(vec![(parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"))], |job| {
            let (a, b) = (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)"));
            let (c, d) = (parse_term("xor(xor(x, y), z)"), parse_term("xor(z, xor(y, x))"));
            let join = move |job: &mut Job, x: &Term, y: &Term| {
                job.rw.memo = Some(RewriteMemo::new(k));
                let (joined, spent) = job.spent(|job| join_eq(job, 4, k, x, y));
                assert!(joined.is_some());
                job.rw.memo.take();
                spent.join.stored
            };
            job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
            join(job, &a, &b);
            let frozen = job.join_store.as_ref().and_then(JoinStoreUse::frozen).expect("the job feeds a store");
            join(job, &c, &d);
            let rules = job.rules().mined().to_vec();
            let setup = job.setup().clone();
            let worker = std::thread::spawn(move || {
                let job = &mut Job::new(setup);
                tatic::kernel::scoped(|| {
                    job.with_mined(rules, |job| {
                        job.join_store = Some(JoinStoreUse::Read(frozen));
                        (join(job, &a, &b), join(job, &c, &d))
                    })
                })
            });
            assert_eq!(worker.join().unwrap(), (1, 0), "the pair joined before the freeze is served, the one after is not");
            assert_eq!(join(job, &c, &d), 1, "the feeding job reads its own store");
            job.join_store = None;
        })
    })
}

/// A stored path is served read either way, through several steps, and after its law moves to another index in the table;
/// the kernel accepts each plan.
#[test]
fn join_store_serves_paths_backwards_through_several_steps_and_moved_laws() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let (n, k) = (4, 3);
        let rule = (parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"));
        let other = (parse_term("sub(x, sub(x, y))"), parse_term("y"));
        let pairs = [
            (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)")),
            (parse_term("xor(xor(x, y), z)"), parse_term("xor(z, xor(y, x))")),
        ];
        let served = |job: &mut Job, a: &Term, b: &Term| {
            job.rw.memo = Some(RewriteMemo::new(k));
            let (plan, spent) = job.spent(|job| join_eq(job, n, k, a, b));
            let plan = plan.expect("joined");
            job.rw.memo.take();
            let (p, s) = law_proof(job, n, k, a, b, &plan);
            job.lemmas.ck("stored", &p, &s);
            spent.join.stored
        };
        let before = job.with_mined(vec![rule], |job| {
            job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
            for (a, b) in &pairs {
                served(job, a, b);
            }
            let (c, d) = &pairs[1];
            assert!(stored_join(job, *d, *c).expect("stored").1.len() > 2, "the xor pair's path has several steps");
            job.rules().table.join_key.clone()
        });
        job.with_mined(vec![other, rule], |job| {
            let after = &job.rules().table.join_key;
            assert!(before.iter().any(|(law, i)| after.get(law).is_some_and(|j| j != i)), "a law moved");
            for (a, b) in &pairs {
                assert_eq!((served(job, b, a), served(job, a, b)), (1, 1), "served backwards and forwards, the rule moved");
            }
        });
        job.join_store = None;
    })
}

/// A search feeds the store only where the store is read (the memo on, no rule blocked): the miner's proofs run on its main
/// thread at 1 thread and on others otherwise, so a store they fed would depend on the thread count.
#[test]
fn join_store_is_fed_only_where_it_is_read() {
    let job = &mut Job::new(Setup::process());
    tatic::kernel::scoped(|| {
        let k = 3;
        let rule = (parse_term("add(sub(add(x, y), -1), z)"), parse_term("add(sub(x, -1), add(y, z))"));
        job.with_mined(vec![rule], |job| {
            let (a, b) = (parse_term("add(add(z, y), sub(x, -1))"), parse_term("add(sub(add(x, y), -1), z)"));
            let join = |job: &mut Job, memo: bool| {
                job.rw.memo = memo.then(|| RewriteMemo::new(k));
                let (joined, spent) = job.spent(|job| join_eq(job, 4, k, &a, &b));
                assert!(joined.is_some());
                job.rw.memo.take();
                spent.join.stored
            };
            job.join_store = Some(JoinStoreUse::Feed(JoinStore::default()));
            join(job, false);
            job.blocked.push(rule);
            join(job, true);
            job.blocked.clear();
            assert_eq!(join(job, true), 0, "searched without the memo and while proving: neither fed the store");
            assert_eq!(join(job, true), 1, "searched with the memo: fed");
            job.join_store = None;
        })
    })
}

/// A memo hit gives what a fresh rewrite would, also under rules that cycle: an entry made where the path was short is replayed
/// inside a call that a fresh rewrite would cut (docs/tier-cycle.md, the law 168 entry under Open).
#[test]
fn memo_hits_match_fresh_rewrites_under_cycling_rules() {
    let job = &mut Job::new(Setup::process());
    let (n, kv) = (4, 3);
    // t = lt(x, sub(y, z)) -> u = lt(x, add(y, z)) -> v = lt(x, or(sub(y, z), y)) -> lt(x, and(..)): t embeds in v, so rewriting t
    // cuts at v, while u on its own (rewritten first, into the memo) does not
    // and t again, replayed from its own entry (its cut was against itself), then u, whose entry made inside t's call is not kept
    let terms: Vec<Term> = ["lt(x, add(y, z))", "lt(x, sub(y, z))", "lt(x, sub(y, z))", "lt(x, add(y, z))"].iter().map(|s| parse_term(s)).collect();
    let rules = "lt(x, sub(y, z)) -> lt(x, add(y, z))\nlt(x, add(y, z)) -> lt(x, or(sub(y, z), y))\nlt(x, or(y, z)) -> lt(x, and(y, z))\n";
    let (fresh, memo) = job.with_mined(parse_rules(rules), |job| {
        let mut run = |memo: Option<RewriteMemo>| {
            job.rw.memo = memo;
            let out: Vec<(String, i64)> = terms
                .iter()
                .map(|t| {
                    let (nf, spent) = job.measured(LAW_STEPS, |job| rewrite(job, t, n, kv).0.show());
                    (nf, spent.steps)
                })
                .collect();
            job.rw.memo.take();
            out
        };
        (run(None), run(Some(RewriteMemo::new(kv))))
    });
    let differ: Vec<_> = terms.iter().zip(fresh.iter().zip(&memo)).filter(|(_, (f, m))| f != m).map(|(t, (f, m))| format!("{}: fresh {f:?} memo {m:?}", t.show())).collect();
    assert!(differ.is_empty(), "{} of {} differ:\n{}", differ.len(), terms.len(), differ.join("\n"));
}

/// A rewrite whose cuts were all against terms its own call took up is kept: any replay cuts them again. One cut against a
/// term further out is not (docs/tier-cycle.md, "Survey: `rewrite_memo`'s 17.4% of CPU").
/// The table's normal form is off: this tests the rules' cuts and memo, which act only where the table does not (spec,
/// Testing).
#[test]
fn memo_keeps_rewrites_cut_inside_their_own_call() {
    let job = &mut Job::new(Setup::with_env(vec![("ABLATE".into(), "classes".into())]));
    let (n, kv) = (4, 3);
    // rewriting t goes t -> u -> v, where t embeds in v: the cut is against t itself; u's own call, inside t's, is cut by t
    let (t, u) = (parse_term("lt(x, sub(y, z))"), parse_term("lt(x, add(y, z))"));
    let rules = parse_rules("lt(x, sub(y, z)) -> lt(x, add(y, z))\nlt(x, add(y, z)) -> lt(x, or(sub(y, z), y))\nlt(x, or(y, z)) -> lt(x, and(y, z))\n");
    job.rw.memo = Some(RewriteMemo::new(kv));
    let (_, spent) = job.measured(LAW_STEPS, |job| job.with_mined(rules, |job| rewrite(job, &t, n, kv)));
    let cut = spent.cycle_cuts > 0;
    let memo = job.rw.memo.take().unwrap();
    assert!(cut, "rewriting t cuts");
    assert!(memo.map.contains_key(&(n, t)), "t's rewrite, cut only against itself, is kept");
    assert!(!memo.map.contains_key(&(n, u)), "u's rewrite inside t's, cut against t, is not");
}

#[test]
pub fn refute_returns_a_witness_for_false_laws_and_none_for_true_ones() {
    let t = |s: &str| parse_term(s);
    for (l, r) in [("add(x, y)", "add(y, x)"), ("xor(x, x)", "0"), ("sub(add(x, y), y)", "x")] {
        assert!(t(l).refute(&t(r), 2).is_none(), "{l} = {r} is a law");
    }
    for (l, r) in [("lt(x, y)", "lt(y, x)"), ("sub(x, y)", "sub(y, x)"), ("and(x, y)", "or(x, y)"), ("shl1(x, 0)", "x")] {
        let (l, r) = (t(l), t(r));
        let (w, vals) = l.refute(&r, 2).unwrap_or_else(|| panic!("{} = {} is false", l.show(), r.show()));
        assert_ne!(l.interp(w, &vals), r.interp(w, &vals), "witness for {} = {}", l.show(), r.show());
    }
}

#[test]
fn term_interning() {
    let (x, y) = (Term::v(0), Term::v(1));
    let a = Term::op(ADD, x, Term::op(XOR, y, Term::ONES));
    let b = Term::op(ADD, x, Term::op(XOR, y, Term::ONES));
    assert!(std::ptr::eq(a.node(), b.node()));
    assert!(a != Term::op(ADD, Term::op(XOR, y, Term::ONES), x));
    // built on 8 threads at once: one node per term
    let built: Vec<Vec<Term>> = std::thread::scope(|s| {
        let hs: Vec<_> = (0..8)
            .map(|_| s.spawn(|| (0..200).map(|i| Term::op(i % 8, Term::v(i % 5), Term::op(AND, Term::v(i % 7), Term::ZERO))).collect::<Vec<_>>()))
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    for w in &built[1..] {
        assert!(w.iter().zip(&built[0]).all(|(p, q)| std::ptr::eq(p.node(), q.node())));
    }
    assert_eq!((std::mem::size_of::<Term>(), std::mem::size_of::<Node>()), (8, 32));
}

#[test]
fn term_attributes_match_a_walk() {
    fn walk(t: &Term) -> (usize, Vec<usize>) {
        match *t.node() {
            Node::V(i) => (1, vec![i]),
            Node::Op(_, a, b) => {
                let ((sa, mut va), (sb, vb)) = (walk(&a), walk(&b));
                va.extend(vb);
                (1 + sa + sb, va)
            }
            _ => (1, vec![]),
        }
    }
    let high = Term::op(XOR, Term::op(AND, Term::v(63), Term::v(9)), Term::v(40));
    let ts: Vec<Term> = PIN_SOURCE.iter().map(|s| parse_term(s)).chain([high, Term::ZERO, Term::ONES, Term::v(0)]).collect();
    for t in &ts {
        let (size, vars) = walk(t);
        assert_eq!(t.size(), size, "{}", t.size());
        assert_eq!(t.max_var(), vars.iter().copied().max().unwrap_or(0));
        assert!((0..70).all(|v| t.has_var(v) == vars.contains(&v)));
    }
}

#[test]
fn rule_table_lists_every_matching_rule_in_order() {
    let job = &Job::new(Setup::process());
    // built-in rules plus run-time ones with a variable, a leaf and a nested operand at the root's operands
    let mined = parse_rules("x -> and(x, x)\nsub(0, x) -> x\nadd(sub(x, y), z) -> sub(add(x, z), y)\n");
    let table = RuleTable::new(job.setup(), mined);
    let mut leaves: Vec<Term> = vec![Term::ZERO, Term::ONES, Term::v(0)];
    leaves.extend(terms(job.setup(), 3, true).iter().copied());
    let (mut tried, mut skipped) = (0, 0);
    for t in &leaves {
        let ids: Vec<usize> = table.candidates(t).map(|(i, _)| i).collect();
        assert!(ids.windows(2).all(|w| w[0] < w[1]), "{}: out of order", t.show());
        for (i, r) in table.rules.iter().enumerate().filter(|(_, r)| !job.setup().ablated(r.name)) {
            if match_pat(&r.lhs, t, &mut [None; RULE_VARS]) {
                assert!(ids.contains(&i), "{}: {} matches but is not a candidate", t.show(), r.lhs.show());
            }
        }
        tried += ids.len();
        skipped += table.rules.len() - ids.len();
    }
    assert!(skipped > 0 && tried > 0, "{tried} tried, {skipped} skipped");
}

/// `PatIndex::get` offers every pattern that matches a term, and for a pattern whose repeated variables all lie within
/// depth 2 only those: it checks the shape down to the grandchildren, a leaf's own class, and that the positions within
/// depth 2 holding one variable hold one subterm.
#[test]
fn pat_index_offers_only_matches_down_to_grandchildren() {
    let pats = ["and(x, or(y, 0))", "and(x, or(y, z))", "0", "add(x, x)", "y", "-1", "or(and(x, -1), y)", "or(and(x, y), and(y, x))", "or(x, and(x, 0))"];
    let pats: Vec<Term> = pats.map(parse_term).to_vec();
    let ix = PatIndex::new(pats.iter().enumerate().map(|(i, p)| (i, p, ())));
    let mut terms = vec![Term::v(0), Term::v(1), Term::ZERO, Term::ONES];
    for _ in 0..2 {
        let level: Vec<Term> = terms.iter().flat_map(|&a| terms.iter().flat_map(move |&b| [ADD, AND, OR].map(|o| Term::op(o, a, b)))).collect();
        terms.extend(level);
    }
    let mut matched = vec![0; pats.len()];
    for t in &terms {
        let offered: Vec<usize> = ix.get(t).map(|(i, ())| i).collect();
        for (i, p) in pats.iter().enumerate() {
            let m = match_pat(p, t, &mut [None; RULE_VARS]);
            assert!(m == offered.contains(&i), "{} {} {} but is{} offered", p.show(), if m { "matches" } else { "does not match" }, t.show(), if m { " not" } else { "" });
            matched[i] += m as usize;
        }
    }
    assert!(matched.iter().all(|&m| m > 0) && matched.iter().sum::<usize>() > 1000, "matched {matched:?}");
}

#[test]
fn value_memo_matches_interp() {
    // the screen as it was before `ValueMemo`: both sides evaluated on each tuple in turn
    fn old_counterexample(a: &Term, b: &Term, n: usize, k: usize, tries: usize) -> Option<Vec<u128>> {
        let mask = low_bits(n);
        let mut seed = 0x9e37_79b9_7f4a_7c15u128;
        (0..tries).find_map(|i| {
            let vals: Vec<u128> = (0..k)
                .map(|_| {
                    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                    match i {
                        0 => 0,
                        1 => mask,
                        _ => (seed >> 40) & mask,
                    }
                })
                .collect();
            (a.interp(n, &vals) != b.interp(n, &vals)).then_some(vals)
        })
    }
    let ts: Vec<Term> = PIN_SOURCE.iter().map(|s| parse_term(s)).chain([Term::ZERO, Term::ONES]).collect();
    let k = ts.iter().map(|t| t.max_var() + 1).max().unwrap();
    for n in [1, 4, 64, 128] {
        for a in &ts {
            for b in &ts {
                for tries in [16, SCREEN_INPUTS] {
                    let old = old_counterexample(a, b, n, k, tries);
                    assert_eq!(a.differs_in(b, n, k, tries), old.is_some());
                    assert_eq!(a.counterexample_in(b, n, k, tries), old, "{} vs {} at {n}", a.show(), b.show());
                }
            }
        }
    }
    let mut memo = ValueMemo::exhaustive(3, 2);
    for t in ts.iter().filter(|t| t.max_var() < 2) {
        let want: Vec<u8> = (0..64u128).map(|i| t.interp(3, &[i & 7, i >> 3]) as u8).collect();
        assert_eq!(memo.values(t), want, "{}", t.show());
    }
}

#[test]
fn term_order_is_the_old_derived_order() {
    let mut ts: Vec<Term> = PIN_SOURCE.iter().map(|s| parse_term(s)).collect();
    ts.sort();
    let got: Vec<String> = ts.iter().map(|t| t.show()).collect();
    assert_eq!(got, PINNED);
    for t in &ts {
        assert!(parse_term(&t.show()) == *t);
    }
    // variables past VARS (renamed apart) sort by index, before every other leaf
    assert!(Term::v(9) < Term::v(10) && Term::v(63) < Term::ZERO && Term::ZERO < Term::ONES);
}
/// Terms in no particular order; `PINNED` is their sort under the old derived `Ord`, captured at main's HEAD.
const PIN_SOURCE: [&str; 38] = [
    "add(x, add(y, z))", "x", "and(add(x, y), -1)", "-1", "add(y, x)", "q", "xor(x, -1)", "0", "add(x, y)",
    "add(add(x, y), z)", "add(x, x)", "and(x, y)", "or(x, 0)", "sub(-1, x)", "lt(x, y)", "shl1(x, x)", "shr1(y, y)",
    "add(add(x, y), y)", "add(add(x, z), y)", "and(add(x, y), 0)", "xor(and(x, y), or(x, y))", "xor(and(x, y), or(y, x))",
    "or(and(x, y), and(x, z))", "sub(add(x, y), y)", "sub(x, sub(x, y))", "lt(sub(x, y), 0)", "shl1(add(x, y), x)",
    "add(shl1(x, x), 0)", "add(0, x)", "add(-1, x)", "add(u, v)", "add(w, p)", "and(-1, 0)", "y",
    "xor(xor(x, y), xor(z, u))", "xor(xor(x, y), xor(z, v))", "add(add(add(x, y), z), u)", "add(x, add(y, add(z, u)))",
];
const PINNED: [&str; 38] = [
    "x",
    "y",
    "q",
    "0",
    "-1",
    "add(x, x)",
    "add(x, y)",
    "add(x, add(y, z))",
    "add(x, add(y, add(z, u)))",
    "add(y, x)",
    "add(u, v)",
    "add(w, p)",
    "add(0, x)",
    "add(-1, x)",
    "add(add(x, y), y)",
    "add(add(x, y), z)",
    "add(add(x, z), y)",
    "add(add(add(x, y), z), u)",
    "add(shl1(x, x), 0)",
    "and(x, y)",
    "and(-1, 0)",
    "and(add(x, y), 0)",
    "and(add(x, y), -1)",
    "or(x, 0)",
    "or(and(x, y), and(x, z))",
    "xor(x, -1)",
    "xor(and(x, y), or(x, y))",
    "xor(and(x, y), or(y, x))",
    "xor(xor(x, y), xor(z, u))",
    "xor(xor(x, y), xor(z, v))",
    "sub(x, sub(x, y))",
    "sub(-1, x)",
    "sub(add(x, y), y)",
    "lt(x, y)",
    "lt(sub(x, y), 0)",
    "shl1(x, x)",
    "shl1(add(x, y), x)",
    "shr1(y, y)",
];
