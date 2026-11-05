use super::*;

/// A hash-consed term: a pointer to its one node. Leaves are statics, `Op` nodes are interned (`Term::op`) and never
/// freed, so equal terms are the same pointer: `==` and `Hash` take the address, and clone is a copy. Each node also
/// carries what is computed bottom-up once, when it is made: its size, the set of its variables and its shape.
/// `show()` is for text (files, logs, lemma names). `Ord` is the order of that text, without building it.
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
pub(super) fn sh_op(o: usize, a: u64, b: u64) -> u64 {
    mix(a ^ mix(b.wrapping_add(o as u64)))
}
// Shape bits: 0..8 an operator at the root; 8..61 (operator, side, child `class`), the 176 of them folded into 53 bits;
// 61, 62, 63 a leaf V, Ones, Zero. `RuleTable` keeps exact per-operand class masks instead: it tests one term at a time,
// where the folding would only admit rules that cannot match.
const fn side_bit(o: usize, side: usize, c: usize) -> u64 {
    1 << (8 + ((o * 2 + side) * CLASSES + c) % 53)
}
const _: () = assert!(OP_INFO.len() <= 8, "the shape has bits 0..8 for the operator at the root");
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
    pub(super) fn addr(self) -> u64 {
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
    pub(super) fn sh(&self) -> u64 {
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

impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.addr().hash(h)
    }
}
/// `self.show().cmp(&other.show())` without the text: the order the rewriter sorts operands by, the stream builds sort
/// terms by and the run-time rules and mined files are kept in. Equal heads give equal text up to the operands, so the
/// first differing head in preorder decides by its token (a name or constant). A token that is a prefix of another (`x`
/// of `xor`) is followed in the text by `,`, `)`, `(` or the end, all below any token character, so the shorter token is
/// the lesser, as `str` compares them. A variable past `VARS` (renamed apart) has no text; it sorts after `z`, by index.
impl Ord for Term {
    fn cmp(&self, other: &Term) -> std::cmp::Ordering {
        fn token(n: Node) -> (&'static str, usize) {
            match n {
                Node::V(i) if i < VARS.len() => (VARS[i], 0),
                Node::V(i) => ("z", i + 1 - VARS.len()),
                Node::Zero => ("0", 0),
                Node::Ones => ("-1", 0),
                Node::Op(o, ..) => (OP_INFO[o].name, 0),
            }
        }
        if self == other {
            return std::cmp::Ordering::Equal;
        }
        match (*self.node(), *other.node()) {
            (Node::Op(o, a, b), Node::Op(p, c, d)) if o == p => a.cmp(&c).then_with(|| b.cmp(&d)),
            (x, y) => token(x).cmp(&token(y)),
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
    pub words: Words,
}
/// One operator on words as a byte (exhaustive values, width at most 8) and as a `u128` (the screen, `Term::interp`): a
/// row cannot hold one function generic over `Word`, and a byte loop given the `u128` one stays `u128` arithmetic.
pub struct Words {
    pub w8: fn(u8, u8, u8) -> u8,
    pub w128: fn(u128, u128, u128) -> u128,
}
/// `Words` from one body over `x`, `y` and `mask`, written once and typed twice.
macro_rules! words {
    (|$x:pat_param, $y:pat_param, $m:pat_param| $body:expr) => {
        Words { w8: |$x: u8, $y: u8, $m: u8| -> u8 { $body }, w128: |$x: u128, $y: u128, $m: u128| -> u128 { $body } }
    };
}
const fn info(name: &'static str, carries: bool, bitwise: bool, shift: bool, prec: i32, truth: fn(bool, bool) -> bool, words: Words) -> OpInfo {
    OpInfo { name, carries, bitwise, shift, prec, truth, words }
}
fn no_truth(_: bool, _: bool) -> bool {
    panic!("not a bitwise operator")
}
/// Every fact about an operator, indexed as `Node::Op` (the one place that says what each computes and which ops carry,
/// are bitwise or shift).
pub const OP_INFO: [OpInfo; 8] = [
    info("add", true, false, false, 6, no_truth, words!(|x, y, m| x.wrapping_add(y) & m)),
    info("and", false, true, false, 3, |a, b| a && b, words!(|x, y, _| x & y)),
    info("or", false, true, false, 2, |a, b| a || b, words!(|x, y, _| x | y)),
    info("xor", false, true, false, 4, |a, b| a != b, words!(|x, y, _| x ^ y)),
    info("sub", true, false, false, 5, no_truth, words!(|x, y, m| x.wrapping_sub(y) & m)),
    info("lt", true, false, false, 1, no_truth, words!(|x, y, _| (x < y) as _)),
    info("shl1", true, false, true, 0, no_truth, words!(|x, _, m| (x << 1) & m)),
    info("shr1", false, false, true, 0, no_truth, words!(|x, _, _| x >> 1)),
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
        self.show_into(&mut s).expect("a String takes any text");
        s
    }
    /// `show`'s text, written into `out`: a `String`, or `search::Fnv` to hash it without building it.
    pub fn show_into(&self, out: &mut impl std::fmt::Write) -> std::fmt::Result {
        match *self.node() {
            Node::V(i) => out.write_str(VARS[i]),
            Node::Zero => out.write_char('0'),
            Node::Ones => out.write_str("-1"),
            Node::Op(o, a, b) => {
                out.write_str(OP_INFO[o].name)?;
                out.write_char('(')?;
                a.show_into(out)?;
                out.write_str(", ")?;
                b.show_into(out)?;
                out.write_char(')')
            }
        }
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
                (OP_INFO[o].words.w128)(x, y, mask)
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

