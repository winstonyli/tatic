use super::*;

/// A hash-consed term: a pointer to its one node. Leaves are statics, `Op` nodes are interned (`Term::op`) and never
/// freed, so equal terms are the same pointer: `==` and `Hash` take the address, and clone is a copy. Each node also
/// carries what is computed bottom-up once, when it is made: its size and the set of its variables.
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
}
impl Interned {
    const fn leaf(node: Node, vars: u64) -> Interned {
        Interned { node, size: 1, vars }
    }
}
static LEAVES: [Interned; 64] = {
    let mut a = [const { Interned::leaf(Node::Zero, 0) }; 64];
    let mut i = 0;
    while i < 64 {
        a[i] = Interned::leaf(Node::V(i), 1 << i);
        i += 1;
    }
    a
};
// The leaf consts name statics: a promoted `&Interned` need not have one address.
static ZERO_NODE: Interned = Interned::leaf(Node::Zero, 0);
static ONES_NODE: Interned = Interned::leaf(Node::Ones, 0);
const SHARDS: usize = 16;
static TABLE: [std::sync::Mutex<hashbrown::HashTable<&'static Interned>>; SHARDS] =
    [const { std::sync::Mutex::new(hashbrown::HashTable::new()) }; SHARDS];
/// The table's hash of `Op(o, a, b)`: unseeded, so every call agrees (a default-built seeded hasher may not).
fn op_hash(o: usize, a: Term, b: Term) -> u64 {
    let mut h = o as u64 ^ a.addr().rotate_left(21) ^ b.addr().rotate_left(43);
    h ^= h >> 33;
    h = h.wrapping_mul(0xff51_afd7_ed55_8ccd);
    h ^= h >> 33;
    h = h.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    h ^ h >> 33
}
impl Term {
    pub const ZERO: Term = Term(&ZERO_NODE);
    pub const ONES: Term = Term(&ONES_NODE);
    pub fn v(i: usize) -> Term {
        assert!(i < LEAVES.len(), "variable {i} past the leaf table");
        Term(&LEAVES[i])
    }
    /// The one node `Op(o, a, b)`, made on first sight. The shard is bits 40..44 of the hash, which hashbrown uses
    /// for neither its tag (top 7 bits) nor its bucket (low bits).
    pub fn op(o: usize, a: Term, b: Term) -> Term {
        let (h, n) = (op_hash(o, a, b), Node::Op(o, a, b));
        let mut t = TABLE[(h >> 40) as usize % SHARDS].lock().unwrap();
        if let Some(&m) = t.find(h, |m| m.node == n) {
            return Term(m);
        }
        let m: &'static Interned = Box::leak(Box::new(Interned { node: n, size: 1 + a.0.size + b.0.size, vars: a.0.vars | b.0.vars }));
        t.insert_unique(h, m, |m| match m.node {
            Node::Op(o, a, b) => op_hash(o, a, b),
            _ => unreachable!("only Op nodes are interned"),
        });
        Term(m)
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
/// How many of `OP_INFO` the miner enumerates: `sub` only with `MINER_SUB=1`.
pub fn nops() -> usize {
    if std::env::var("MINER_SUB").is_ok() { 5 } else { 4 }
}
/// The environment variable `k` parsed as `T`, or `d` when unset or unparsable (every experiment knob reads through this).
pub fn env_or<T: std::str::FromStr>(k: &str, d: T) -> T {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}
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
        let mask = low_bits(n);
        match *self.node() {
            Node::V(i) => vals[i],
            Node::Zero => 0,
            Node::Ones => mask,
            Node::Op(o, a, b) => {
                let (x, y) = (a.interp(n, vals), b.interp(n, vals));
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

/// A `ValueMemo` block's size in bytes (one vector when a vector is larger).
const VALUE_BLOCK: usize = 1 << 16;

/// The screen's input count: all zeros, all ones, then 202 pseudo-random tuples.
const SCREEN_INPUTS: usize = 204;

thread_local! {
    /// The plausibility screen's value memos, by width and variable count.
    static SCREENS: std::cell::RefCell<hashbrown::HashMap<(usize, usize), ValueMemo<u128>>> = Default::default();
}

/// `f` on the screen's value memo for width `n` and `k` variables.
fn with_screen<R>(n: usize, k: usize, f: impl FnOnce(&mut ValueMemo<u128>) -> R) -> R {
    SCREENS.with(|s| f(s.borrow_mut().entry((n, k)).or_insert_with(|| ValueMemo::screen(n, k))))
}

impl<W: Word> ValueMemo<W> {
    fn new(n: usize, len: usize, vars: Vec<Box<[W]>>) -> Self {
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
                let zips: [fn(&mut [W], &[W], &[W], u128); OP_INFO.len()] =
                    [zip_word::<W, 0>, zip_word::<W, 1>, zip_word::<W, 2>, zip_word::<W, 3>, zip_word::<W, 4>, zip_word::<W, 5>, zip_word::<W, 6>, zip_word::<W, 7>];
                zips[o](out, at(a), at(b), mask);
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
pub fn terms(nvars: usize, deep: bool) -> std::rc::Rc<[Term]> {
    thread_local! {
        static TERMS: std::cell::RefCell<hashbrown::HashMap<(usize, bool, usize), std::rc::Rc<[Term]>>> = Default::default();
    }
    TERMS.with(|c| c.borrow_mut().entry((nvars, deep, nops())).or_insert_with(|| build_terms(nvars, deep).into()).clone())
}

fn build_terms(nvars: usize, deep: bool) -> Vec<Term> {
    let mut leaves: Vec<Term> = (0..nvars).map(Term::v).collect();
    leaves.push(Term::ZERO);
    leaves.push(Term::ONES);
    let mut level1 = vec![];
    for o in 0..nops() {
        for a in &leaves {
            for b in &leaves {
                level1.push(Term::op(o, *a, *b));
            }
        }
    }
    let mut all = leaves.clone();
    all.extend(level1.clone());
    if deep {
        for o in 0..nops() {
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

thread_local! {
    /// The lemma parameters: one nested scope per bound lemma, outermost first, with the lemma's proof (none for one
    /// loaded from `LEMMA_CACHE`). A proof may use the lemmas bound before it (a mined rule proved through a machine proof
    /// uses its case lemmas).
    pub static PARAMS: std::cell::RefCell<Option<(Postulates, Vec<(Scope, Option<tatic::kernel::PExpr>)>)>> = const { std::cell::RefCell::new(None) };
}
/// `memo` for a closed lemma `(proof, statement)`: the proof is checked once (`ck`, against the lemmas bound before it)
/// and the lemma is returned as a parameter of that statement, so a law using it is checked against the parameter, not
/// the proof. `discharge` turns a term over parameters back into a closed one. A statement an earlier process of the loop
/// checked is bound without building its proof (`lemma_cache`).
pub fn shared_lemma(key: String, build: impl FnOnce() -> (Expr, Expr)) -> (Expr, Expr) {
    memo(key.clone(), || {
        let (p, s) = match lemma_cache::lookup(&key) {
            Some(s) if !lemma_cache::recheck() => (None, s),
            cached => {
                let (p, s) = build();
                ck(&format!("lemma {key}"), &p, &s);
                match cached {
                    Some(c) => assert!(c == s, "LEMMA_RECHECK: the cached statement of {key} is not the one built"),
                    None => lemma_cache::record(&key, &s),
                }
                (Some(p), s)
            }
        };
        PARAMS.with(|c| {
            let mut c = c.borrow_mut();
            let (ps, scopes) = c.get_or_insert_with(|| (Postulates::new(), Vec::new()));
            let sc = ps.open();
            let r = ps.bind(s);
            scopes.push((sc, p.map(tatic::kernel::persist)));
            (r, s)
        })
    })
}
/// `body` with the lemma parameters discharged, innermost first: `(\r_0. .. ((\r_m. body) P_m) ..) P_0`, a closed term
/// whose check re-checks every lemma proof `P_i` once. Ends the scopes; the memoised parameters stay in `CLOSED`, so
/// call it last.
pub fn discharge(body: Expr) -> Expr {
    let Some((mut ps, scopes)) = PARAMS.with(|c| c.borrow_mut().take()) else { return body };
    scopes.into_iter().rev().fold(body, |b, (sc, p)| app(ps.close(sc, Binder::Lam, b), p.expect("discharge needs every lemma's proof: run without LEMMA_CACHE").get()))
}

/// Whether the rewriter's rule `name` is switched off by the env var `ABLATE` (comma list: comm, assoc, chain, tree, collapse,
/// promoted, ruleset, a built-in rule's name, and `prove_eq`'s eq_truth, eq_pos, shrmask). Read once per process: `rule_step`
/// asks for every rule it tries, and reading the environment each time was 11% of a mine (docs/tier-cycle.md).
pub fn ablated(name: &str) -> bool {
    static SET: std::sync::OnceLock<Vec<String>> = std::sync::OnceLock::new();
    SET.get_or_init(|| std::env::var("ABLATE").map(|v| v.split(',').map(String::from).collect()).unwrap_or_default()).iter().any(|x| x == name)
}

/// `(value, GoodBv witness)` of `t` in context `[x, y, gx, gy]`.
pub fn witnessed(t: &Term, n: usize, goods: &[(Expr, Expr)]) -> (Expr, Expr) {
    let all = low_bits(n);
    match *t.node() {
        Node::V(i) => goods[i],
        Node::Zero => (lit(n, 0), good_lit(n, 0)),
        Node::Ones => (lit(n, all), good_lit(n, all)),
        Node::Op(o, a, b) => {
            let ((av, aw), (bv, bw)) = (witnessed(&a, n, goods), witnessed(&b, n, goods));
            let (op, good_op) = match o {
                0 => (add(n), shared_lemma(format!("good_add{n}"), || good_add(n)).0),
                4 => (sub(n), shared_lemma(format!("good_sub{n}"), || good_sub(n)).0),
                6 => (shl1_op(n), shared_lemma(format!("good_shl1{n}"), || good_shl1(n)).0),
                7 => (shr1_op(n), shared_lemma(format!("good_shr1{n}"), || good_shr1(n)).0),
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
    pub fn refl(t: &Term) -> PlanRc {
        PlanRc::new(Plan::Refl(*t))
    }
    pub fn cong(o: usize, a: PlanRc, b: PlanRc) -> PlanRc {
        PlanRc::new(Plan::Cong(o, a, b))
    }
    pub fn trans(a: PlanRc, b: PlanRc) -> PlanRc {
        PlanRc::new(Plan::Trans(a, b))
    }
    pub fn sym(a: PlanRc) -> PlanRc {
        PlanRc::new(Plan::Sym(a))
    }
    pub fn law(kind: LawKind, lhs: Term, rhs: Term, args: Vec<Term>) -> PlanRc {
        PlanRc::new(Plan::Law(kind, lhs, rhs, args))
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
    pub fn proof(&self, plan: &Plan) -> (Term, Term, Expr) {
        let n = self.n;
        match plan {
            Plan::Refl(t) => (*t, *t, refl(self.ev(t))),
            Plan::Cong(o, a, b) => {
                let ((a1, a2, pa), (b1, b2, pb)) = (self.proof(a), self.proof(b));
                let (xs, ys) = ([self.ev(&a1), self.ev(&b1)], [self.ev(&a2), self.ev(&b2)]);
                let (l, r) = (Term::op(*o, a1, b1), Term::op(*o, a2, b2));
                let p = cong_n(&bv_ty(n), &self.ty(&l), &self.ops[*o], &xs, &ys, vec![pa, pb]);
                (l, r, p)
            }
            Plan::Trans(a, b) => {
                let ((x, y, p), (_, z, q)) = (self.proof(a), self.proof(b));
                let p = trans_proof(&self.ty(&x), &self.ev(&x), &self.ev(&y), &self.ev(&z), p, q);
                (x, z, p)
            }
            Plan::Sym(a) => {
                let (x, y, p) = self.proof(a);
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
                let law = shared_lemma(format!("{prover}_{}_{}_{n}_{k}", l.show(), r.show()), || match kind {
                    LawKind::Rule(name) => prove_rule(n, k, l, r).unwrap_or_else(|| panic!("rule {name} is not provable")),
                    LawKind::Assoc => add_assoc_proof(n, false),
                    LawKind::Comm => add_comm_proof(n, false),
                    LawKind::Bitwise => bitwise_law_k(n, k, l, r),
                    LawKind::Chain => carry_chain_law(n, l, r).expect("a constant carry"),
                    LawKind::Tree => add_tree_law(n, k, l, r).expect("a carry encoding"),
                })
                .0;
                let w: Vec<(Expr, Expr)> = args.iter().map(|t| witnessed(t, n, &self.goods)).collect();
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
pub fn chain_step(a: &Term, b: &Term) -> Option<(Term, PlanRc)> {
    if ablated("chain") {
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
    Some((target, Plan::law(LawKind::Chain, Term::op(ADD, a1, b1), cand, args)))
}

/// A sum tree of add-free leaves that the carry-encoding search shows equal to a constant, a variable or one
/// bitwise operation on two of them (so `-1 - x` becomes `x ^ -1`): that value and
/// the plan (`add_tree_law` over the `k` variables). Ablation name `tree`.
pub fn tree_step(n: usize, t1: &Term, k: usize) -> Option<(Term, PlanRc)> {
    if ablated("tree") {
        return None;
    }
    // `tree_encoding` refuses a candidate whose screen values differ from `t1`'s, so only those with `t1`'s vector are tried
    let index = TREE_CANDS.with(|c| c.borrow_mut().entry((n, k, nops())).or_insert_with(|| tree_candidates(n, k)).clone());
    let cand = *with_screen(n, k, |m| index.get(m.values(t1)))?.iter().find(|cand| tree_encoding(n, k, t1, cand).is_some())?;
    Some((cand, Plan::law(LawKind::Tree, *t1, cand, vars(k))))
}

thread_local! {
    /// `tree_step`'s candidates by their screen vector, per width, variable count and operator count (`tree_candidates`).
    static TREE_CANDS: std::cell::RefCell<hashbrown::HashMap<(usize, usize, usize), std::rc::Rc<CandIndex>>> = Default::default();
}

/// Candidates by screen vector, each list in candidate order.
type CandIndex = hashbrown::HashMap<Box<[u128]>, Vec<Term>>;

/// `tree_step`'s candidates, the constants, the variables, then every operator applied to two of them, indexed by their
/// screen vector: one lookup finds those `t1` could equal, where trying each took ~79 screen comparisons a step
/// (docs/tier-cycle.md, "What the screen does in a sweep").
fn tree_candidates(n: usize, k: usize) -> std::rc::Rc<CandIndex> {
    let mut index = CandIndex::default();
    with_screen(n, k, |m| {
        for cand in [Term::ZERO, Term::ONES]
            .into_iter()
            .chain((0..k).map(Term::v))
            .chain(terms(k, false).iter().copied().filter(|c| matches!(*c.node(), Node::Op(o, ..) if (1..=3).contains(&o))))
        {
            index.entry(m.values(&cand).into()).or_insert_with(Vec::new).push(cand);
        }
    });
    index.into()
}

/// A library law used as a left-to-right rewrite rule: `lhs = rhs` over the pattern variables `V(0)..`, each instance
/// proved from the law `add_tree_law` proves once (per width) for the patterns themselves. `name` is the `ABLATE` key.
pub struct Rule {
    pub name: &'static str,
    pub lhs: Term,
    pub rhs: Term,
}

thread_local! {
    /// Set by the rule miner while scoring (`RULEMINER_FAST=1`): `prove_eq` takes a machine fallback when a few tuples agree,
    /// without searching for its carry encoding, so a plan made under it may not compile.
    pub static SCORE_ONLY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The rules `rule_step` tries: the built-in ones, then those added at run time (by the rule miner) in `set_extra_rules`
    /// order. Write it only through `set_extra_rules`.
    pub static RULE_TABLE: std::cell::RefCell<RuleTable> = std::cell::RefCell::new(RuleTable::new(vec![]));
    /// While `Some`, `rule_step` records every term it is asked to rewrite, and whether a rule fired on it: a rule added anywhere
    /// in the rule list can change a rewriting only if its left side matches one of them, and one added last only if it matches
    /// one where no rule fired (unless a preference makes it a winner).
    pub static RULE_TRACE: std::cell::RefCell<Option<Vec<(Term, Fired)>>> = const { std::cell::RefCell::new(None) };
    /// Learned rule preferences, (winner, loser): where both rules would rewrite a term, the winner does, whatever the order
    /// (docs/tier-cycle.md, "Rule order"). Set with the rules they belong to (`set_rule_prefs`).
    pub static RULE_PREFS: std::cell::RefCell<hashbrown::HashSet<Pref>> = Default::default();
}

/// A rule as its two sides, and a preference (winner, loser) between two rules.
pub type RuleKey = (Term, Term);
pub type Pref = (RuleKey, RuleKey);

/// `lhs -> rhs`, the spelling of rule files and logs.
pub fn rule_show((l, r): &RuleKey) -> String {
    format!("{} -> {}", l.show(), r.show())
}

/// The preference lines of a rules file, `winner  OVER  loser` with each side a rule `lhs -> rhs` (`parse_rules` skips them).
pub fn parse_prefs(text: &str) -> Vec<Pref> {
    let rule = |r: &str| r.split_once(" -> ").map(|(l, r)| (parse_term(l.trim()), parse_term(r.trim())));
    text.lines().filter_map(|l| l.split_once("  OVER  ")).filter_map(|(w, l)| Some((rule(w)?, rule(l)?))).collect()
}

/// Installs `prefs` in order: a later preference replaces an earlier one for the same pair the other way round.
pub fn set_rule_prefs(prefs: Vec<Pref>) {
    RULE_PREFS.with(|p| {
        let mut p = p.borrow_mut();
        p.clear();
        for (w, l) in prefs {
            p.remove(&(l, w));
            p.insert((w, l));
        }
    });
}

#[test]
fn preferences_choose_between_rules_that_both_match() {
    let text = "sub(sub(x, y), z) -> sub(x, add(y, z))\nsub(x, sub(y, z)) -> add(sub(x, y), z)\n\
                sub(x, sub(y, z)) -> add(sub(x, y), z)  OVER  sub(sub(x, y), z) -> sub(x, add(y, z))\n";
    assert_eq!(parse_rules(text).len(), 2, "a preference line is not a rule");
    let t = parse_term("sub(sub(x, y), sub(z, u))");
    let step = |prefs: Vec<Pref>| {
        set_extra_rules(parse_rules(text));
        set_rule_prefs(prefs);
        let out = rule_step(&t).unwrap().0.show();
        set_extra_rules(vec![]);
        set_rule_prefs(vec![]);
        out
    };
    // same size, so specific first falls to the text order; the preference overrides it, and a later reverse line undoes it
    let prefs = parse_prefs(text);
    assert_eq!(prefs.len(), 1);
    let (plain, preferred) = (step(vec![]), step(prefs.clone()));
    assert_ne!(plain, preferred);
    assert_eq!(preferred, parse_term("add(sub(sub(x, y), z), u)").show());
    let reverse = (prefs[0].1, prefs[0].0);
    assert_eq!(step(vec![prefs[0], reverse]), plain);
}

/// Installs `rules` as the run-time rules, most specific first: larger left sides first, ties by text. `rule_step` applies the first
/// rule that matches, so a library's order would otherwise change its normal forms: the same pooled library served in six orders
/// gave total M 47-62 on add3 (docs/tier-cycle.md, "Rule order"). Any order of the same rules now serves identically.
pub fn set_extra_rules(mut rules: Vec<(Term, Term)>) {
    rules.sort_by_cached_key(|(l, r)| run_order(l, r));
    RULE_TABLE.with(|e| *e.borrow_mut() = RuleTable::new(rules));
}

/// A rule as `rule_step` tries it, with what does not depend on the term decided when the rule set is installed (deciding
/// it per term, and building the rule list per term, were about 10% of a sweep: docs/tier-cycle.md, "Profile at f447a57").
#[derive(Clone, Copy)]
struct TableRule {
    name: &'static str,
    lhs: Term,
    rhs: Term,
    /// the pattern variables of both sides are `V(0)..V(vars)`
    vars: usize,
    permutative: bool,
}

impl TableRule {
    fn new(name: &'static str, lhs: Term, rhs: Term) -> TableRule {
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

/// The rules `rule_step` tries, in order: the built-in ones, then the run-time ones (`mined`); and for each root operator, and
/// for leaves, the rules in that order that are not ablated and whose left side can match such a term.
pub struct RuleTable {
    pub mined: Vec<(Term, Term)>,
    rules: Vec<TableRule>,
    by_op: [Vec<u32>; OP_INFO.len()],
    leaf: Vec<u32>,
}

impl RuleTable {
    fn new(mined: Vec<(Term, Term)>) -> RuleTable {
        static FIXED: std::sync::OnceLock<Vec<TableRule>> = std::sync::OnceLock::new();
        let fixed = FIXED.get_or_init(|| fixed_rules().iter().map(|r| TableRule::new(r.name, r.lhs, r.rhs)).collect());
        let rules: Vec<TableRule> = fixed.iter().copied().chain(mined.iter().map(|&(l, r)| TableRule::new("mined", l, r))).collect();
        let (mut by_op, mut leaf): ([Vec<u32>; OP_INFO.len()], Vec<u32>) = Default::default();
        for (i, r) in rules.iter().enumerate().filter(|(_, r)| !ablated(r.name)) {
            match *r.lhs.node() {
                Node::Op(o, ..) => by_op[o].push(i as u32),
                Node::V(_) => by_op.iter_mut().chain([&mut leaf]).for_each(|b| b.push(i as u32)),
                Node::Zero | Node::Ones => leaf.push(i as u32),
            }
        }
        RuleTable { mined, rules, by_op, leaf }
    }

    /// The rules that can match `t`, in order.
    fn candidates(&self, t: &Term) -> impl Iterator<Item = (usize, &TableRule)> {
        let ids = match *t.node() {
            Node::Op(o, ..) => &self.by_op[o],
            _ => &self.leaf,
        };
        ids.iter().map(|&i| (i as usize, &self.rules[i as usize]))
    }
}

/// The run-time rules' order key (`set_extra_rules`).
pub fn run_order(l: &Term, r: &Term) -> (std::cmp::Reverse<usize>, String, String) {
    (std::cmp::Reverse(l.size()), l.show(), r.show())
}

/// The first rule that fired on a term `rule_step` was asked about (`RULE_TRACE`): none, a built-in rule (tried before every
/// run-time rule) or a run-time rule.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Fired {
    None,
    Fixed,
    Mined(Term, Term),
}

impl Fired {
    /// A run-time rule added to the rules that made this trace comes first on the term, `before(r)` saying whether it comes
    /// before run-time rule `r` (`run_order`): it rewrites the term if it matches it (and no preference makes another rule win).
    pub fn preempted_by(&self, before: impl Fn(&(Term, Term)) -> bool) -> bool {
        match self {
            Fired::None => true,
            Fired::Fixed => false,
            Fired::Mined(l, r) => before(&(*l, *r)),
        }
    }
}

#[test]
fn rule_order_does_not_change_rewriting() {
    // overlapping rules: under list order the first one would win on sub(sub(x, y), z) whichever it is
    let a = "sub(sub(x, y), z) -> sub(x, add(y, z))\nsub(x, y) -> add(x, sub(0, y))\nsub(sub(x, y), z) -> sub(sub(x, z), y)\n";
    let b = "sub(sub(x, y), z) -> sub(sub(x, z), y)\nsub(x, y) -> add(x, sub(0, y))\nsub(sub(x, y), z) -> sub(x, add(y, z))\n";
    let installed = |text: &str| {
        set_extra_rules(parse_rules(text));
        let shown: Vec<String> = RULE_TABLE.with(|e| e.borrow().mined.iter().map(|(l, r)| format!("{} -> {}", l.show(), r.show())).collect());
        set_extra_rules(vec![]);
        shown
    };
    let (ia, ib) = (installed(a), installed(b));
    assert_eq!(ia, ib);
    assert!(ia.last().unwrap().starts_with("sub(x, y)"), "the general rule goes after the specific ones: {ia:?}");
}
// How many more rule applications `rule_step` may make; the rule miner sets it per trial so that a candidate that
// undoes a built-in rule cannot loop. Soundness is unaffected: a refused step only leaves the term less normalized.
thread_local! {
    pub static RULE_BUDGET: std::cell::Cell<i64> = const { std::cell::Cell::new(i64::MAX / 2) };
    /// Rules being proved by `prove_rule` through the rewriter; `rule_step` skips them.
    pub static PROVING: std::cell::RefCell<Vec<RuleKey>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// The mined rule set selected by `RULESET` (`add3_mm`, `mix3_mm`, `add3_nl`, `mix3_nl`, the files in `scripts/data`; sections 84 and 87), in force
/// after the built-in rules; empty when unset. `ABLATE=ruleset` removes it again. The two sets were mined without
/// `ABLATE=subdist`.
pub fn rule_set() -> &'static Vec<(Term, Term)> {
    static SET: std::sync::OnceLock<Vec<(Term, Term)>> = std::sync::OnceLock::new();
    SET.get_or_init(|| {
        let text = match std::env::var("RULESET").as_deref() {
            Ok("add3_mm") => include_str!("../../scripts/data/add3_mm_rules.txt"),
            Ok("mix3_mm") => include_str!("../../scripts/data/mix3_mm_rules.txt"),
            Ok("add3_nl") => include_str!("../../scripts/data/add3_nl_rules.txt"),
            Ok("mix3_nl") => include_str!("../../scripts/data/mix3_nl_rules.txt"),
            Ok(other) => panic!("unknown RULESET {other}"),
            Err(_) => "",
        };
        parse_rules(text)
    })
}

/// The rules that do not change during a run, in the order `rule_step` tries them: the built-ins, the promoted rules, the
/// `RULESET` rules; the mined ones (`RULE_TABLE`) come after them. Built once per process.
pub fn fixed_rules() -> &'static [Rule] {
    static RULES: std::sync::OnceLock<Vec<Rule>> = std::sync::OnceLock::new();
    RULES.get_or_init(build_fixed_rules)
}

fn build_fixed_rules() -> Vec<Rule> {
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
    all.extend(rule_set().iter().map(|(l, r)| Rule { name: "ruleset", lhs: *l, rhs: *r }));
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

/// The rules of a rule file: one `lhs -> rhs` per line, repeats once, other lines (and preference lines, `parse_prefs`) ignored.
pub fn parse_rules(text: &str) -> Vec<(Term, Term)> {
    let mut seen = hashbrown::HashSet::new();
    text.lines().filter(|l| !l.contains("  OVER  ")).filter_map(|l| l.split_once(" -> ")).map(|(a, b)| (parse_term(a), parse_term(b))).filter(|r| seen.insert(*r)).collect()
}

/// A pooled rules file has a section per library (a `# library <name>` line, then its rules; `driver::sweep`); a rule two
/// libraries share is in both. The sections, in order, with their rules.
pub fn library_sections(text: &str) -> Vec<(String, Vec<(Term, Term)>)> {
    let (mut out, mut open): (Vec<(String, Vec<(Term, Term)>)>, bool) = (vec![], false);
    for l in text.lines() {
        if let Some(n) = l.strip_prefix("# library ") {
            out.push((n.trim().to_string(), vec![]));
            open = true;
        } else if l.contains("  OVER  ") || (!l.trim().is_empty() && !l.contains(" -> ")) {
            // a section holds only rule lines (and blank ones)
            open = false;
        } else if let Some(s) = out.last_mut().filter(|_| open) {
            s.1.extend(parse_rules(l));
        }
    }
    out
}

/// The critical pairs of two rules: for each non-variable position of either left side where the other's (variables renamed
/// apart) unifies, the two results of rewriting that most general instance once by each rule. Variables are renumbered from 0 in
/// order of appearance.
pub fn critical_pairs(r1: &(Term, Term), r2: &(Term, Term)) -> Vec<(Term, Term)> {
    fn shift(t: &Term, k: usize) -> Term {
        match *t.node() {
            Node::V(i) => Term::v(i + k),
            Node::Op(o, a, b) => Term::op(o, shift(&a, k), shift(&b, k)),
            _ => *t,
        }
    }
    // `t` with one non-variable position unified with `l` and replaced by `r`, and the unifier
    fn at(t: &Term, l: &Term, r: &Term, nv: usize) -> Vec<(Vec<Option<Term>>, Term)> {
        let mut out = vec![];
        if let Node::Op(o, a, b) = *t.node() {
            let mut s = vec![None; nv];
            if unify(t, l, &mut s) {
                out.push((s, *r));
            }
            out.extend(at(&a, l, r, nv).into_iter().map(|(s, a2)| (s, Term::op(o, a2, b))));
            out.extend(at(&b, l, r, nv).into_iter().map(|(s, b2)| (s, Term::op(o, a, b2))));
        }
        out
    }
    fn apply(t: &Term, s: &[Option<Term>]) -> Term {
        match *t.node() {
            Node::V(i) => s[i].as_ref().map_or_else(|| *t, |b| apply(b, s)),
            Node::Op(o, a, b) => Term::op(o, apply(&a, s), apply(&b, s)),
            _ => *t,
        }
    }
    fn renumber(t: &Term, seen: &mut Vec<usize>) -> Term {
        match *t.node() {
            Node::V(i) => Term::v(seen.iter().position(|j| *j == i).unwrap_or_else(|| {
                seen.push(i);
                seen.len() - 1
            })),
            Node::Op(o, a, b) => Term::op(o, renumber(&a, seen), renumber(&b, seen)),
            _ => *t,
        }
    }
    let mut out = vec![];
    for (p, q) in [(r1, r2), (r2, r1)] {
        let k = p.0.max_var().max(p.1.max_var()) + 1;
        let (lq, rq) = (shift(&q.0, k), shift(&q.1, k));
        let nv = k + lq.max_var().max(rq.max_var()) + 1;
        for (s, inner) in at(&p.0, &lq, &rq, nv) {
            let mut seen = vec![];
            let (x, y) = (renumber(&apply(&p.1, &s), &mut seen), renumber(&apply(&inner, &s), &mut seen));
            out.push((x, y));
        }
    }
    out
}

/// The units a pooled library's rules can be dropped in: for each two libraries A and B, B's rules (not also A's) that `meet` a
/// rule of A's (the miner: a critical pair that does not join). Where two families orient rules into different normal forms,
/// those are the rules that meet (docs/tier-cycle.md, "Salt 2's pooled add3 loss", "Drop units"); a single rule or a whole
/// library is the wrong size.
pub fn drop_units(sections: &[(String, Vec<(Term, Term)>)], meet: &dyn Fn(&(Term, Term), &(Term, Term)) -> bool) -> Vec<Vec<(Term, Term)>> {
    let mut units: Vec<Vec<(Term, Term)>> = vec![];
    for (a, (_, ra)) in sections.iter().enumerate() {
        for (_, rb) in sections.iter().enumerate().filter(|&(b, _)| b != a).map(|(_, s)| s) {
            let unit: Vec<(Term, Term)> = rb.iter().filter(|r| !ra.contains(r) && ra.iter().any(|x| meet(r, x))).cloned().collect();
            if !unit.is_empty() && !units.contains(&unit) {
                units.push(unit);
            }
        }
    }
    units
}

/// The drop units of a pooled rules file (`library_sections`), where two rules meet when a critical pair of theirs does not
/// join: rewritten (over `n` bits, `steps` per side) under all the file's rules and preferences, its two sides reach different
/// normal forms. They depend only on the file, so `driver::sweep` builds them once (`units_text`) for every family's mine.
pub fn joinability_units(text: &str, n: usize, steps: i64) -> Vec<Vec<(Term, Term)>> {
    set_extra_rules(parse_rules(text));
    set_rule_prefs(parse_prefs(text));
    let joins = |a: &Term, b: &Term| {
        let k = a.max_var().max(b.max_var()) + 1;
        let side = |t: &Term| {
            RULE_BUDGET.with(|c| c.set(steps));
            rewrite(t, n, k).0
        };
        side(a) == side(b)
    };
    let units = drop_units(&library_sections(text), &|r, x| critical_pairs(r, x).iter().any(|(a, b)| !joins(a, b)));
    set_extra_rules(vec![]);
    set_rule_prefs(vec![]);
    RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
    units
}

/// Drop units as text: a unit's rules one per line, units separated by blank lines (`parse_units`).
pub fn units_text(units: &[Vec<(Term, Term)>]) -> String {
    units.iter().map(|u| u.iter().map(|(l, r)| format!("{} -> {}\n", l.show(), r.show())).collect::<String>()).collect::<Vec<_>>().join("\n")
}

pub fn parse_units(text: &str) -> Vec<Vec<(Term, Term)>> {
    text.split("\n\n").map(parse_rules).filter(|u| !u.is_empty()).collect()
}

#[test]
fn drop_units_are_the_rules_meeting_another_library() {
    let text = "# library a\nsub(sub(x, y), z) -> sub(x, add(y, z))\nor(x, x) -> x\n# library b\nsub(sub(x, y), z) -> sub(sub(x, z), y)\nsub(x, sub(y, z)) -> add(sub(x, y), z)\nor(x, x) -> x\nand(x, 0) -> 0\nsub(x, 0) -> x  OVER  or(x, x) -> x\n";
    let s = library_sections(text);
    assert_eq!(s.iter().map(|s| (s.0.as_str(), s.1.len())).collect::<Vec<_>>(), [("a", 2), ("b", 4)]);
    assert_eq!(parse_rules(text).len(), 5, "a rule two libraries share is one rule");
    // here two rules meet when they overlap at all (the miner asks for a critical pair that does not join)
    let u = drop_units(&s, &|r, a| !critical_pairs(r, a).is_empty());
    let shown = |u: &[(Term, Term)]| u.iter().map(|(l, r)| format!("{} -> {}", l.show(), r.show())).collect::<Vec<_>>();
    // both of b's sub rules unify with a's sub(sub(x, y), z) at the root; the shared or rule and b's and rule meet nothing of a's
    assert_eq!(shown(&u[0]), ["sub(sub(x, y), z) -> sub(sub(x, z), y)", "sub(x, sub(y, z)) -> add(sub(x, y), z)"]);
    assert_eq!(shown(&u[1]), ["sub(sub(x, y), z) -> sub(x, add(y, z))"]);
    assert_eq!(u.len(), 2);
}

#[test]
fn critical_pairs_of_two_orientations() {
    let r = parse_rules("sub(sub(x, y), z) -> sub(x, add(y, z))\nsub(sub(x, y), z) -> sub(sub(x, z), y)\nor(x, x) -> x\n");
    let shown: Vec<String> = critical_pairs(&r[0], &r[1]).iter().map(|(a, b)| format!("{} | {}", a.show(), b.show())).collect();
    // at the root, both ways; and each left side's inner sub(x, y) under the other's
    assert!(shown.contains(&"sub(x, add(y, z)) | sub(sub(x, z), y)".to_string()), "{shown:?}");
    assert!(shown.contains(&"sub(sub(x, y), z) | sub(x, add(z, y))".to_string()), "{shown:?}");
    assert_eq!(shown.len(), 4, "{shown:?}");
    assert!(critical_pairs(&r[0], &r[2]).is_empty());
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
pub fn shr_not_law(n: usize) -> Option<(Expr, Expr)> {
    let b = |o: usize, x: Term, y: Term| Term::op(o, x, y);
    let (l, r) = shrnot_rule();
    let m = b(SHR1, b(XOR, Term::v(0), Term::ONES), Term::ZERO);
    let own = (l, r);
    let notsub = fixed_rules().iter().find(|x| x.name == "notsub").map(|x| (x.lhs, x.rhs))?;
    let prove = |blocked: &[RuleKey], t1: &Term, t2: &Term| proving(blocked, || rewrite_law(n, 1, t1, t2));
    let to_left = prove(std::slice::from_ref(&own), &m, &l)?;
    let to_right = prove(&[own, notsub], &m, &r)?;
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
pub fn prove_rule(n: usize, k: usize, l: &Term, r: &Term) -> Option<(Expr, Expr)> {
    if (l, r) == (&shrnot_rule().0, &shrnot_rule().1) {
        shr_not_law(n)
    } else if l.add_free() && r.add_free() {
        let law = bitwise_law_k(n, k, l, r);
        holds(&law.0, &law.1).ok().map(|_| law)
    } else if matches!(*l.node(), Node::Op(SHR1, ..)) && matches!(*r.node(), Node::Op(SHR1, ..) | Node::Zero) || matches!(*r.node(), Node::Op(SHR1, ..)) && matches!(*l.node(), Node::Zero) {
        // laws with a `shr1` root are not machines: prove them with the rewriter (which falls back on the bit-0 mask
        // reduction), without the rule being proved, so that it cannot be used in its own proof
        proving(&[(*l, *r)], || rewrite_law(n, k, l, r))
    } else {
        add_tree_law(n, k, l, r)
    }
}

/// `f` (a proof of a rule by rewriting, with the rules `blocked`) run as a rewriting job of its own: its own cycle path and
/// step budget, no memo (`REWRITE_MEMO` holds results under all the rules), no trace, and its machine fallbacks not counted
/// for the caller, whose rewriting it does not change.
fn proving<T>(blocked: &[RuleKey], f: impl FnOnce() -> T) -> T {
    let outer = PROVING.with(|p| p.borrow().len());
    PROVING.with(|p| p.borrow_mut().extend(blocked.iter().cloned()));
    let path = REWRITE_PATH.with(|p| p.take());
    let memo = REWRITE_MEMO.with(|m| m.take());
    let trace = RULE_TRACE.with(|t| t.take());
    let budget = RULE_BUDGET.with(|b| b.replace(10_000));
    let (fallbacks, cuts) = (MACHINE_FALLBACKS.with(|c| c.get()), CYCLE_CUTS.with(|c| c.get()));
    let out = f();
    PROVING.with(|p| p.borrow_mut().truncate(outer));
    REWRITE_PATH.with(|p| p.replace(path));
    REWRITE_MEMO.with(|m| m.replace(memo));
    RULE_TRACE.with(|t| t.replace(trace));
    RULE_BUDGET.with(|b| b.set(budget));
    MACHINE_FALLBACKS.with(|c| c.set(fallbacks));
    CYCLE_CUTS.with(|c| c.set(cuts));
    out
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
/// occurrences (a tie-break, not a termination proof: `RULE_BUDGET` backs it up, and `rule_step` skips a rewrite that
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
    match (*p.node(), *t.node()) {
        (Node::V(i), _) => match &sub[i] {
            Some(b) => b == t,
            None => {
                sub[i] = Some(*t);
                true
            }
        },
        (Node::Zero, Node::Zero) | (Node::Ones, Node::Ones) => true,
        (Node::Op(o, a, b), Node::Op(o2, c, d)) => o == o2 && match_pat(&a, &c, sub) && match_pat(&b, &d, sub),
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
    let rules = parse_rules(&std::fs::read_to_string(std::env::var("OVERLAP_RULES").expect("set OVERLAP_RULES=<file>")).unwrap());
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

/// Print every rule application (set by the `normal_forms` debug test).
pub static TRACE_RULES: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Instances of `rule_step` by rule name, for the audit.
pub static RULE_HITS: std::sync::Mutex<Vec<(&'static str, u64)>> = std::sync::Mutex::new(Vec::new());

/// `RULE_CONFLICTS=1` (experiment): for each (rule that rewrote a term, later rule that would also have), how many terms; `print_rule_conflicts` lists them.
pub static RULE_CONFLICTS: std::sync::Mutex<Option<hashbrown::HashMap<Pref, u64>>> = std::sync::Mutex::new(None);

pub fn print_rule_conflicts() {
    if let Some(m) = RULE_CONFLICTS.lock().unwrap().as_ref() {
        let mut v: Vec<_> = m.iter().map(|((w, l), c)| (rule_show(w), rule_show(l), *c)).collect();
        v.sort_by_key(|(w, l, c)| (std::cmp::Reverse(*c), w.clone(), l.clone()));
        for (w, l, c) in &v {
            println!("CONFLICT {c} {w}  OVER  {l}");
        }
        println!("CONFLICTS {} pairs, {} terms", v.len(), v.iter().map(|x| x.2).sum::<u64>());
    }
}

/// The first library rule (not ablated) whose left side matches `t`: the rewritten term and the plan.
pub fn rule_step(t: &Term) -> Option<(Term, PlanRc)> {
    RULE_TABLE.with(|table| rule_step_in(t, &table.borrow()))
}

fn rule_step_in(t: &Term, table: &RuleTable) -> Option<(Term, PlanRc)> {
    let all = &table.rules;
    let fires = |r: &TableRule| -> Option<[Option<Term>; RULE_VARS]> {
        let mut sub = [None; RULE_VARS];
        if !match_pat(&r.lhs, t, &mut sub) {
            return None;
        }
        if PROVING.with(|p| p.borrow().iter().any(|k| r.is(k))) {
            return None;
        }
        // a rule whose right side is an instance of its own left side (`lt(x,x) -> lt(-1,-1)`) must not rewrite its result
        let inst = subst_pat(&r.rhs, &sub.map(|s| s.or(Some(Term::ZERO))));
        if inst == *t {
            return None;
        }
        // a permutative rule (ordered rewriting): only when the instance goes down in the order on `show()` strings
        // (a path order on every tied instance, `PERM_ORDER=lpo`, raised M, and the tie-break order before `show()`, `PERM_ORDER=tie`,
        // never became the default; the rewrite cycles both targeted are cut in `rewrite` instead: docs/tier-cycle.md)
        if r.permutative && inst.show_cmp(t).is_ge() {
            return None;
        }
        Some(sub)
    };
    let first = table.candidates(t).find_map(|(i, r)| fires(r).map(|s| (i, s)));
    RULE_TRACE.with(|tr| {
        if let Some(v) = tr.borrow_mut().as_mut() {
            v.push((
                *t,
                match first {
                    None => Fired::None,
                    Some((i, _)) if all[i].name == "mined" => Fired::Mined(all[i].lhs, all[i].rhs),
                    Some(_) => Fired::Fixed,
                },
            ));
        }
    });
    let (mut i, mut sub) = first?;
    RULE_PREFS.with(|prefer| {
        let prefer = prefer.borrow();
        if prefer.is_empty() {
            return;
        }
        // follow preferences from the first rule that fires; at most one hop per rule, so a preference cycle stops
        for _ in 0..all.len() {
            let winners: Vec<&RuleKey> = prefer.iter().filter(|(_, l)| all[i].is(l)).map(|(w, _)| w).collect();
            if winners.is_empty() {
                break;
            }
            match table.candidates(t).find_map(|(j, r)| if j != i && winners.iter().any(|w| r.is(w)) { fires(r).map(|s| (j, s)) } else { None }) {
                Some(next) => (i, sub) = next,
                None => break,
            }
        }
    });
    if let Some(m) = RULE_CONFLICTS.lock().unwrap().as_mut() {
        for (_, r) in table.candidates(t).filter(|&(j, r)| j > i && fires(r).is_some()) {
            *m.entry((all[i].key(), r.key())).or_default() += 1;
        }
    }
    let r = &all[i];
    if TRACE_RULES.load(std::sync::atomic::Ordering::Relaxed) {
        println!("TRACE {} -> {}   on {}", r.lhs.show(), r.rhs.show(), t.show());
    }
    if RULE_BUDGET.with(|b| b.replace(b.get() - 1)) <= 0 {
        return None;
    }
    // a pattern variable the left side does not mention is free in the law: any value serves
    let args = sub[..r.vars].iter().map(|s| s.unwrap_or(Term::v(0))).collect();
    let mut hits = RULE_HITS.lock().unwrap();
    match hits.iter_mut().find(|h| h.0 == r.name) {
        Some(h) => h.1 += 1,
        None => hits.push((r.name, 1)),
    }
    Some((subst_pat(&r.rhs, &sub), Plan::law(LawKind::Rule(r.name), r.lhs, r.rhs, args)))
}

/// A cached `rewrite`: the result and what the call did besides returning it, so that a hit can replay it.
struct Rewritten {
    out: (Term, PlanRc),
    /// rule steps used (`RULE_BUDGET`): a hit needs at least this many left
    steps: i64,
    fallbacks: u64,
    /// the terms `rule_step` was asked about and whether a rule fired (`RULE_TRACE`), when `traced` (the trace was on)
    trace: Vec<(Term, Fired)>,
    traced: bool,
    /// the terms the call took up below its own (`REWROTE`), once each: a replay is right only where the path cuts none of them
    rewrote: Vec<Term>,
}

/// While `Some`, `rewrite` calls over `k` variables are cached by (width, term). The rule miner sets it for one rule set
/// (one `score_laws` call): the result of `rewrite` is a function of the term, the rules in force and the budget left, so a repeat
/// under the same rules is a hit. Calls over other variable counts (the generalization path adds witnesses) are not cached.
pub struct RewriteMemo {
    k: usize,
    map: hashbrown::HashMap<(usize, Term), std::rc::Rc<Rewritten>>,
}

impl RewriteMemo {
    pub fn new(k: usize) -> RewriteMemo {
        RewriteMemo { k, map: Default::default() }
    }

    /// The traced entries whose traces `keep` accepts. A rule tried after the others changes no entry whose trace it matches
    /// nowhere among the terms no rule fired on, so the rule miner seeds each candidate's scoring with the entries of the rules
    /// chosen so far that the candidate cannot change.
    pub fn filtered(&self, keep: impl Fn(&[(Term, Fired)]) -> bool) -> RewriteMemo {
        // presized to the whole memo (an upper bound): grown from empty, the map rehashed several times per candidate
        let mut map = hashbrown::HashMap::with_capacity(self.map.len());
        map.extend(self.map.iter().filter(|(_, e)| e.traced && keep(&e.trace)).map(|(k, e)| (*k, e.clone())));
        RewriteMemo { k: self.k, map }
    }

    pub fn absorb(&mut self, other: RewriteMemo) {
        self.map.extend(other.map);
    }
}

thread_local! {
    pub static REWRITE_MEMO: std::cell::RefCell<Option<RewriteMemo>> = const { std::cell::RefCell::new(None) };
    /// the terms `rewrite` is working on, outermost first, and how many calls it cut so far
    static REWRITE_PATH: std::cell::RefCell<Vec<Term>> = const { std::cell::RefCell::new(Vec::new()) };
    pub static CYCLE_CUTS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// the terms `rewrite` took up (pushed on the path) since the outermost call began, memo replays included
    static REWROTE: std::cell::RefCell<Vec<Term>> = const { std::cell::RefCell::new(Vec::new()) };
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
pub fn rewrite(t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    if !matches!(*t.node(), Node::Op(..)) {
        return rewrite_memo(t, n, k);
    }
    if REWRITE_PATH.with(|p| cut_by(&p.borrow(), t)) {
        CYCLE_CUTS.with(|c| c.set(c.get() + 1));
        return (*t, Plan::refl(t));
    }
    REWRITE_PATH.with(|p| p.borrow_mut().push(*t));
    REWROTE.with(|r| r.borrow_mut().push(*t));
    let out = rewrite_memo(t, n, k);
    if REWRITE_PATH.with(|p| p.borrow_mut().pop().is_some() && p.borrow().is_empty()) {
        REWROTE.with(|r| r.borrow_mut().clear());
    }
    out
}

/// The cycle cut's test: `t` repeats, or grows from, a term on `path`.
fn cut_by(path: &[Term], t: &Term) -> bool {
    let size = t.size();
    path.iter().any(|s| s.size() <= size && embeds(s, t))
}

fn rewrite_memo(t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    let on = matches!(*t.node(), Node::Op(..)) && REWRITE_MEMO.with(|m| m.borrow().as_ref().is_some_and(|m| m.k == k));
    if !on {
        return rewrite_uncached(t, n, k);
    }
    let key = (n, *t);
    let hit = REWRITE_MEMO.with(|m| m.borrow().as_ref().and_then(|m| m.map.get(&key).cloned()));
    // the entry was made with no cut, so the path in force now must cut none of the terms it took up either
    let fits = |c: &Rewritten| RULE_BUDGET.with(|b| b.get()) >= c.steps && REWRITE_PATH.with(|p| !c.rewrote.iter().any(|v| cut_by(&p.borrow(), v)));
    if let Some(c) = hit.filter(|c| fits(c)) {
        #[cfg(debug_assertions)]
        check_replay(t, n, k, &c);
        RULE_BUDGET.with(|b| b.set(b.get() - c.steps));
        MACHINE_FALLBACKS.with(|f| f.set(f.get() + c.fallbacks));
        RULE_TRACE.with(|tr| {
            if let Some(v) = tr.borrow_mut().as_mut() {
                v.extend(c.trace.iter().cloned());
            }
        });
        REWROTE.with(|r| r.borrow_mut().extend(c.rewrote.iter().copied()));
        return c.out.clone();
    }
    let (budget0, fallbacks0, trace0) = (RULE_BUDGET.with(|b| b.get()), MACHINE_FALLBACKS.with(|f| f.get()), RULE_TRACE.with(|tr| tr.borrow().as_ref().map(|v| v.len())));
    let (cuts0, rewrote0) = (CYCLE_CUTS.with(|c| c.get()), REWROTE.with(|r| r.borrow().len()));
    let out = rewrite_uncached(t, n, k);
    let budget1 = RULE_BUDGET.with(|b| b.get());
    // a call that ran the budget out was cut short by it: its result depends on the budget it started with; one with a cycle cut
    // depends on the terms being rewritten further out
    if budget1 > 0 && CYCLE_CUTS.with(|c| c.get()) == cuts0 {
        let trace = RULE_TRACE.with(|tr| tr.borrow().as_ref().map(|v| v[trace0.unwrap_or(0)..].to_vec()).unwrap_or_default());
        let mut seen = hashbrown::HashSet::new();
        let rewrote = REWROTE.with(|r| r.borrow()[rewrote0..].iter().copied().filter(|t| seen.insert(*t)).collect());
        let entry = Rewritten { out: out.clone(), steps: budget0 - budget1, fallbacks: MACHINE_FALLBACKS.with(|f| f.get()) - fallbacks0, trace, traced: trace0.is_some(), rewrote };
        REWRITE_MEMO.with(|m| {
            if let Some(m) = m.borrow_mut().as_mut() {
                m.map.insert(key, std::rc::Rc::new(entry));
            }
        });
    }
    out
}

/// Debug builds: a memo hit about to be replayed is redone without the memo, under the same path and budget, and must match it
/// (the law 168 bug was a replay a fresh rewrite would have cut). Only `RULE_HITS` and `RULE_CONFLICTS` keep the redo's counts.
#[cfg(debug_assertions)]
fn check_replay(t: &Term, n: usize, k: usize, c: &Rewritten) {
    let memo = REWRITE_MEMO.with(|m| m.take());
    let trace = RULE_TRACE.with(|t| t.take());
    let (budget, fallbacks, cuts, rewrote) =
        (RULE_BUDGET.with(|b| b.get()), MACHINE_FALLBACKS.with(|f| f.get()), CYCLE_CUTS.with(|c| c.get()), REWROTE.with(|r| r.borrow().len()));
    let fresh = rewrite_uncached(t, n, k);
    let (steps, fresh_fallbacks) = (budget - RULE_BUDGET.with(|b| b.get()), MACHINE_FALLBACKS.with(|f| f.get()) - fallbacks);
    REWRITE_MEMO.with(|m| m.replace(memo));
    RULE_TRACE.with(|t| t.replace(trace));
    RULE_BUDGET.with(|b| b.set(budget));
    MACHINE_FALLBACKS.with(|f| f.set(fallbacks));
    CYCLE_CUTS.with(|c| c.set(cuts));
    REWROTE.with(|r| r.borrow_mut().truncate(rewrote));
    let show = |(t, s, f): (Term, i64, u64)| format!("{} in {s} steps, {f} fallbacks", t.show());
    assert!(
        (fresh.0, steps, fresh_fallbacks) == (c.out.0, c.steps, c.fallbacks),
        "memo replay of {}: {} where a fresh rewrite gives {}",
        t.show(),
        show((c.out.0, c.steps, c.fallbacks)),
        show((fresh.0, steps, fresh_fallbacks))
    );
}

fn rewrite_uncached(t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    let Node::Op(o, a, b) = *t.node() else { return (*t, Plan::refl(t)) };
    // children first: trying the library rules on a node before its children are normalized raised M 3x (docs/tier-cycle.md, "Rule order")
    let ((a2, pa), (b2, pb)) = (rewrite(&a, n, k), rewrite(&b, n, k));
    let cong = Plan::cong(o, pa, pb);
    let t1 = Term::op(o, a2, b2);
    if o != ADD {
        // the library rules first (`shldist`, ...)
        if let Some((target, step)) = rule_step(&t1) {
            let (t3, p3) = rewrite(&target, n, k);
            return (t3, Plan::trans(Plan::trans(cong, step), p3));
        }
        if o == SUB {
            // a difference: then the carry-encoding search
            return match tree_step(n, &t1, k) {
                Some((target, law)) => (target, Plan::trans(cong, law)),
                None => (t1, cong),
            };
        }
        if matches!(o, LT | SHL1 | SHR1) {
            return (t1, cong);
        }
        // bitwise and shift terms only: a node equal to 0, -1 or one of its own subterms collapses to it, by the
        // per-position prover (the truth-table collapse below treats a shift as an atom)
        if let (false, true, true) = (ablated("collapse"), t1.add_free(), t1.has_shift()) {
            let mut subs = vec![];
            t1.subterms(&mut subs);
            let cands = [Term::ZERO, Term::ONES].into_iter().chain(subs.into_iter().skip(1).filter(|c| c.size() < t1.size()));
            if let Some(c) = cands.into_iter().find(|c| c.add_free() && t1.is_law(c, k)) {
                return (c, Plan::trans(cong, Plan::law(LawKind::Bitwise, t1, c, vars(k))));
            }
        }
        // a bitwise node equal to 0, -1 or one of its atoms collapses to it (truth table, then `bitwise_law`)
        let mut atoms = vec![];
        if let (false, Some(abs)) = (ablated("collapse"), abstract_atoms(&t1, &mut atoms, k)) {
            let truth = |t: &Term| (0..1usize << k).map(|m| term_gb(&Bools, t, &(0..k).map(|v| m >> v & 1 == 1).collect::<Vec<_>>())).collect::<Vec<_>>();
            let want = truth(&abs);
            let cands: Vec<Term> = [Term::ZERO, Term::ONES].into_iter().chain((0..k).map(Term::v)).collect();
            if let Some(c) = cands.iter().find(|c| c.max_var() < atoms.len().max(1) && truth(c) == want) {
                let target = if let Node::V(i) = *c.node() { atoms[i] } else { *c };
                if target != t1 {
                    let args = (0..k).map(|i| atoms.get(i).cloned().unwrap_or(Term::v(0))).collect();
                    return (target, Plan::trans(cong, Plan::law(LawKind::Bitwise, abs, *c, args)));
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
            let law = Plan::law(LawKind::Bitwise, swap(Term::v(0), Term::v(1)), swap(Term::v(1), Term::v(0)), vec![a2, b2]);
            return (swap(b2, a2), Plan::trans(cong, law));
        }
        return (t1, cong);
    }
    let sum = |p: &Term, q: &Term| Term::op(ADD, *p, *q);
    let (x, y, z) = (Term::v(0), Term::v(1), Term::v(2));
    let assoc = |p: &Term, q: &Term, r: &Term| Plan::law(LawKind::Assoc, sum(&sum(&x, &y), &z), sum(&x, &sum(&y, &z)), vec![*p, *q, *r]);
    let comm = |p: &Term, q: &Term| Plan::law(LawKind::Comm, sum(&x, &y), sum(&y, &x), vec![*p, *q]);
    // `x + 0` and `x + ~x` are constant-carry sums (`chain_step`); steps of their own were removed as redundant
    let step = if let Some(r) = rule_step(&t1) {
        Some(r)
    } else if let Some(r) = chain_step(&a2, &b2) {
        Some(r)
    } else if let Some(r) = tree_step(n, &t1, k) {
        Some(r)
    } else if let (false, Node::Op(ADD, p, q)) = (ablated("assoc"), *a2.node()) {
        // (p + q) + r = p + (q + r)
        Some((sum(&p, &sum(&q, &b2)), assoc(&p, &q, &b2)))
    } else if let (false, Node::Op(ADD, bp, bq)) = (ablated("assoc") || ablated("comm"), *b2.node()) {
        if bp.show_cmp(&a2).is_lt() {
            // a + (b + c) = (a + b) + c = (b + a) + c = b + (a + c)
            let (a_, b_, c_) = (&a2, &bp, &bq);
            let swapped = Plan::cong(ADD, comm(a_, b_), Plan::refl(c_));
            Some((sum(b_, &sum(a_, c_)), Plan::trans(Plan::trans(Plan::sym(assoc(a_, b_, c_)), swapped), assoc(b_, a_, c_))))
        } else {
            None
        }
    } else if !ablated("comm") && b2.show_cmp(&a2).is_lt() {
        Some((sum(&b2, &a2), comm(&a2, &b2)))
    } else {
        None
    };
    match step {
        None => (t1, cong),
        Some((t2, p)) => {
            let (t3, p3) = rewrite(&t2, n, k);
            (t3, Plan::trans(Plan::trans(cong, p), p3))
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

// How many times `prove_eq` closed a pair with a whole-term machine proof (the rewriting did not finish the job).
// Per thread, so that the parallel miner's workers each read their own before/after difference.
thread_local! {
    pub static MACHINE_FALLBACKS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
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
/// bit values, so the kernel check cannot fail); the per-position law; the bit-0 mask reduction; or the whole-term machine
/// proof. `None` otherwise.
pub fn prove_eq(n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    if a == b {
        return Some(Plan::refl(a));
    }
    // each step below can be switched off: `ABLATE=eq_truth,eq_pos,shrmask`
    let mut atoms = vec![];
    if let (false, Some(a1), Some(a2)) = (ablated("eq_truth"), abstract_atoms(a, &mut atoms, k), abstract_atoms(b, &mut atoms, k)) {
        let holds = (0..1usize << k).all(|m| {
            let bits: Vec<bool> = (0..k).map(|v| m >> v & 1 == 1).collect();
            term_gb(&Bools, &a1, &bits) == term_gb(&Bools, &a2, &bits)
        });
        if holds {
            let args = (0..k).map(|i| atoms.get(i).cloned().unwrap_or(Term::v(0))).collect();
            return Some(Plan::law(LawKind::Bitwise, a1, a2, args));
        }
    }
    // add-free terms with shifts: the per-position prover, when the law holds exhaustively at widths 1..=5 (a position
    // reads only a few neighbours, so widths this small contain every case; the kernel checks the proof regardless)
    if !ablated("eq_pos") && k <= 3 && a.add_free() && b.add_free() && (a.has_shift() || b.has_shift()) {
        let holds = (1..=5usize).all(|w| (0..1u128 << (w * k)).all(|i| {
            let vals: Vec<u128> = (0..k).map(|v| (i >> (w * v)) & low_bits(w)).collect();
            a.interp(w, &vals) == b.interp(w, &vals)
        }));
        if holds {
            return Some(Plan::law(LawKind::Bitwise, *a, *b, vars(k)));
        }
    }
    // congruence on equal operators and generalizing a shared subterm into a variable were removed: neither decided a law
    // (docs/tier-cycle.md, "Ablating the fixed rewriter and prover parts")
    if let Some(p) = shr_mask_eq(n, k, a, b) {
        return Some(p);
    }
    machine_fallback(n, k, a, b)
}

/// The whole-term machine proof of `a = b` (the carry-encoding proof for the two terms as bit-serial machines), counted in
/// `MACHINE_FALLBACKS`; `None` when there is none.
fn machine_fallback(n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    let cost = |t: &Term| Machine::parse(t).map_or(0, |m| m.carries());
    // scoring mode: only whether the rewriting needed this fallback matters, so count it without searching for the encoding (the
    // plan may then not compile); a pair that is not equal fails here as it would in `tree_encoding` (else congruence on unequal
    // operands would count two proofs); a few tuples suffice to tell, since unequal pairs differ almost everywhere
    let screened = SCORE_ONLY.with(|s| s.get()) && Machine::parse(a).is_some() && Machine::parse(b).is_some() && cost(a).max(cost(b)) <= carry_cap();
    if screened && a.differs_in(b, n, k, 16) || !screened && tree_encoding(n, k, a, b).is_none() {
        return None;
    }
    MACHINE_FALLBACKS.with(|c| c.set(c.get() + 1));
    Some(Plan::law(LawKind::Tree, *a, *b, vars(k)))
}

/// `shr1 A = shr1 B` (or `0 = shr1 B`, as `shr1 0`) for machine-expressible `A`, `B`, without a lookahead machine: the
/// bit-0 mask law `shr1 t = shr1 (t & M)`, `M = shl1 -1`, turns the pair into the shift-free law `A & M = B & M`
/// (search note section 47).
pub fn shr_mask_eq(n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    let shr = |t: &Term| Term::op(SHR1, *t, Term::ZERO);
    let (mask, one_arg) = (Term::op(SHL1, Term::ONES, Term::ZERO), |t: &Term| match *t.node() {
        Node::Op(SHR1, x, _) if Machine::parse(&x).is_some() => Some(x),
        Node::Zero => Some(Term::ZERO),
        _ => None,
    });
    if ablated("shrmask") || !matches!(*a.node(), Node::Op(SHR1, ..)) && !matches!(*b.node(), Node::Op(SHR1, ..)) {
        return None;
    }
    let (x, y) = (one_arg(a)?, one_arg(b)?);
    // the pair `A & M`, `B & M`: rewrite both, close with `prove_eq` (a machine law when they stay arithmetic)
    let (ta, tb) = (Term::op(AND, x, mask), Term::op(AND, y, mask));
    let ((r1, p1), (r2, p2)) = (rewrite(&ta, n, k), rewrite(&tb, n, k));
    let mid = prove_eq(n, k, &r1, &r2)?;
    let cong = Plan::cong(SHR1, Plan::trans(p1, Plan::trans(mid, Plan::sym(p2))), Plan::refl(&Term::ZERO));
    // `a = shr1 (A & M)` and `b = shr1 (B & M)`
    let side_proof = |orig: &Term, arg: &Term| -> Option<PlanRc> {
        if matches!(*orig.node(), Node::Zero) {
            // `0 = shr1 0 = shr1 (0 & M)`: the second step is a congruence on `0 = 0 & M` by the rewriter
            let (r, pr) = rewrite(&Term::op(AND, Term::ZERO, mask), n, k);
            if r != Term::ZERO {
                return None;
            }
            let (target, step) = rule_step(&shr(&Term::ZERO))?;
            if target != Term::ZERO {
                return None;
            }
            Some(Plan::trans(Plan::sym(step), Plan::cong(SHR1, Plan::sym(pr), Plan::refl(&Term::ZERO))))
        } else {
            Some(Plan::law(LawKind::Rule("shrmask"), shr(&Term::v(0)), shr(&Term::op(AND, Term::v(0), mask)), vec![*arg]))
        }
    };
    let (pa, pb) = (side_proof(a, &x)?, side_proof(b, &y)?);
    Some(Plan::trans(Plan::trans(pa, cong), Plan::sym(pb)))
}

/// The plan of `t1 = t2` over `k` variables: both sides rewritten, then closed with `prove_eq`; `None` when that cannot.
pub fn rewrite_plan(n: usize, k: usize, t1: &Term, t2: &Term) -> Option<PlanRc> {
    // an `lt` root (a one-bit result) is rewritten under its operands, then closed by congruence or, failing that,
    // by the `lt` machine proof for the rewritten pair; `lt` occurs only at the root
    let lt_roots = matches!((*t1.node(), *t2.node()), (Node::Op(LT, ..), Node::Op(LT, ..)));
    // each side gets the whole `RULE_BUDGET`, so a side that cycles cannot leave the other half-normalized; afterwards the
    // budget is what the hungrier side left, so `RULE_BUDGET <= 0` still says some side used it up
    let budget0 = RULE_BUDGET.with(|b| b.get());
    let ((r1, p1), left1) = (rewrite(t1, n, k), RULE_BUDGET.with(|b| b.replace(budget0)));
    let (r2, p2) = rewrite(t2, n, k);
    RULE_BUDGET.with(|b| b.set(b.get().min(left1)));
    let (p1, p2, mid) = if lt_roots {
        // `rewrite` normalizes the operands and applies the root rules; equal results close by `refl`, `lt` roots with
        // provable operands by congruence, the rest by the `lt` machine proof of the rewritten pair
        let mid = if r1 == r2 {
            Plan::refl(&r1)
        } else {
            let by_operands = if let (Node::Op(LT, a2, b2), Node::Op(LT, c2, d2)) = (*r1.node(), *r2.node()) {
                match (prove_eq(n, k, &a2, &c2), prove_eq(n, k, &b2, &d2)) {
                    (Some(pa), Some(pb)) => Some(Plan::cong(LT, pa, pb)),
                    _ => None,
                }
            } else {
                None
            };
            match by_operands {
                Some(plan) => plan,
                None => machine_fallback(n, k, &r1, &r2)?,
            }
        };
        (p1, p2, mid)
    } else {
        match prove_eq(n, k, &r1, &r2) {
            Some(mid) => (p1, p2, mid),
            // the rewriter may have pushed the shifts down to atoms; the mask reduction applies to the original sides
            None => (Plan::refl(t1), Plan::refl(t2), shr_mask_eq(n, k, t1, t2)?),
        }
    };
    Some(Plan::trans(Plan::trans(p1, mid), Plan::sym(p2)))
}

/// Proof of `t1 = t2` over `k` good vectors: `rewrite_plan`, compiled. `None` when there is no plan.
pub fn rewrite_law(n: usize, k: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    let plan = rewrite_plan(n, k, t1, t2)?;
    Some(law_proof(n, k, t1, t2, &plan))
}

/// The closed law `forall x.. gx... t1 = t2` proved by `plan`.
pub fn law_proof(n: usize, k: usize, t1: &Term, t2: &Term, plan: &Plan) -> (Expr, Expr) {
    let c = Compiler::new(n, k);
    let bv = bv_ty(n);
    let root = if matches!((*t1.node(), *t2.node()), (Node::Op(LT, ..), Node::Op(LT, ..))) { bv_ty(1) } else { bv };
    let (mut proof, mut stmt) = (c.proof(plan).2, id(root, c.ev(t1), c.ev(t2)));
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
/// bit-0 mask): the plan is the same while counting (`SCORE_ONLY`) as while proving, its sides are the law's, and it compiles to
/// a proof the kernel accepts.
#[test]
fn plans_compile_to_checked_proofs() {
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
                SCORE_ONLY.with(|s| s.set(counting));
                rewrite_plan(4, k, l, r).unwrap_or_else(|| panic!("no plan for {} = {} (counting: {counting})", l.show(), r.show()))
            });
            SCORE_ONLY.with(|s| s.set(false));
            let sides = plans.each_ref().map(|p| {
                let (a, b, _) = Compiler::new(4, k).proof(p);
                (a, b)
            });
            assert!(sides[0] == sides[1] && sides[0] == (*l, *r), "{} = {}", l.show(), r.show());
            let (p, s) = law_proof(4, k, l, r, &plans[0]);
            ck(&format!("{} = {}", l.show(), r.show()), &p, &s);
        }
    })
}

#[test]
pub fn laws_over_three_vectors_check_and_false_ones_fail() {
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        for n in [1usize, 3] {
            // bitwise (x ^ y) ^ z = x ^ (y ^ z)
            let (p, s) = bitwise_law_k(n, 3, &op(3, op(3, v(0), v(1)), v(2)), &op(3, v(0), op(3, v(1), v(2))));
            ck(&format!("xor assoc at n={n}"), &p, &s);
            assert!(holds(&bitwise_law_k(n, 3, &op(1, v(0), v(2)), &op(2, v(0), v(2))).0, &bitwise_law_k(n, 3, &op(1, v(0), v(2)), &op(2, v(0), v(2))).1).is_err());
            // add associativity over three vectors, and a non-law
            let (p, s) = rewrite_law(n, 3, &op(0, op(0, v(0), v(1)), v(2)), &op(0, v(0), op(0, v(1), v(2)))).expect("assoc");
            ck(&format!("add assoc at n={n}"), &p, &s);
            let (p, s) = rewrite_law(n, 3, &op(0, op(0, v(2), v(0)), v(1)), &op(0, v(1), op(0, v(0), v(2)))).expect("comm+assoc");
            ck(&format!("add comm assoc at n={n}"), &p, &s);
            assert!(rewrite_law(n, 3, &op(0, v(0), v(2)), &op(0, v(0), v(1))).is_none());
        }
    })
}

#[test]
pub fn rewrite_law_proves_add_conjectures_from_the_library_lemmas() {
    let v = |i: usize| Term::v(i);
    let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
    let n = 4;
    for (name, t1, t2) in [
        ("or (add x 0) y = or y x", op(2, op(0, v(0), Term::ZERO), v(1)), op(2, v(1), v(0))),
        ("xor (add x y) y = xor y (add y x)", op(3, op(0, v(0), v(1)), v(1)), op(3, v(1), op(0, v(1), v(0)))),
        ("add (and x y) y = add y (and y x)", op(0, op(1, v(0), v(1)), v(1)), op(0, v(1), op(1, v(1), v(0)))),
    ] {
        let (p, s) = rewrite_law(n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no rewrite proof"));
        ck(name, &p, &s);
    }
    // associativity instances, including one that needs reordering as well
    for (name, t1, t2) in [
        ("add (add x y) y = add x (add y y)", op(0, op(0, v(0), v(1)), v(1)), op(0, v(0), op(0, v(1), v(1)))),
        ("add (add y y) x = add (add x y) y", op(0, op(0, v(1), v(1)), v(0)), op(0, op(0, v(0), v(1)), v(1))),
    ] {
        let (p, s) = rewrite_law(n, 2, &t1, &t2).unwrap_or_else(|| panic!("{name}: no rewrite proof"));
        ck(name, &p, &s);
    }
    // a false law is refused by the truth-table pre-check
    assert!(rewrite_law(n, 2, &op(0, v(0), v(1)), &op(0, v(0), v(0))).is_none());
}

#[test]
pub fn a_law_over_lemma_parameters_discharges_to_a_closed_proof() {
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::v(i);
        let op = |o: usize, a: Term, b: Term| Term::op(o, a, b);
        let (p, s) = rewrite_law(2, 3, &op(0, op(0, v(2), v(0)), v(1)), &op(0, v(1), op(0, v(0), v(2)))).expect("comm+assoc");
        assert!(PARAMS.with(|c| c.borrow().as_ref().is_some_and(|(.., b)| !b.is_empty())), "no lemma was bound");
        assert!(check(&Ctx::new(), &p, &s).is_err(), "a proof over lemma parameters is not closed");
        ck("over parameters", &p, &s);
        // a machine proof's case lemmas are parameters too
        let add = |a: Term, b: Term| op(0, a, b);
        let (pm, sm) = add_tree_law(2, 3, &add(add(v(0), v(1)), v(2)), &add(v(0), add(v(1), v(2)))).expect("assoc3");
        assert!(check(&Ctx::new(), &pm, &sm).is_err(), "the machine proof's lemmas are not parameters");
        ck("machine over parameters", &pm, &sm);
        // a lemma whose proof uses lemmas bound before it: a rule proved through a machine proof
        let scopes = || PARAMS.with(|c| c.borrow().as_ref().map_or(0, |(_, b)| b.len()));
        let before = scopes();
        let (l, r) = (add(op(4, v(0), v(1)), v(2)), add(op(4, v(2), v(1)), v(0)));
        let (pr, sr) = shared_lemma("nested".into(),|| prove_rule(2, 3, &l, &r).expect("rule"));
        assert!(scopes() >= before + 2, "the rule's proof bound no lemma of its own");
        let all = apps(lam(sm, lam(shift(&s, 0, 1), lam(shift(&sr, 0, 2), var(2)))), vec![pm, p, pr]);
        ck("discharged", &discharge(all), &sm);
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

/// sbo3's rewrite cycle (docs/tier-cycle.md, "Why ordered sbo3 still cycled"): two rules and a permutative one bring
/// `sub(sub(z, x), sub(y, z))` back to itself. `rewrite` cuts it, so the law is proved without using up the step budget, and the
/// proof checks.
#[test]
fn rewrite_cycles_are_cut() {
    tatic::kernel::scoped(|| {
        let rules = "sub(sub(x, y), z) -> sub(x, add(y, z))\nadd(x, sub(y, z)) -> sub(x, sub(z, y))\nsub(x, sub(y, z)) -> sub(z, sub(y, x))\n";
        set_extra_rules(parse_rules(rules));
        RULE_BUDGET.with(|b| b.set(200));
        let cuts0 = CYCLE_CUTS.with(|c| c.get());
        let (t1, t2) = (parse_term("sub(sub(z, x), sub(y, z))"), parse_term("sub(add(z, z), add(x, y))"));
        let out = rewrite_law(4, 3, &t1, &t2);
        let (cuts, left) = (CYCLE_CUTS.with(|c| c.get()) - cuts0, RULE_BUDGET.with(|b| b.get()));
        set_extra_rules(vec![]);
        RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
        println!("cuts {cuts}, budget left {left}, proved {}", out.is_some());
        assert!(cuts > 0, "no cycle cut");
        assert!(left > 0, "the step budget ran out");
        let (p, s) = out.expect("proved");
        ck("cycle law", &p, &s);
    })
}

/// cmp3d's growing chain (docs/tier-cycle.md, "Growth cut"): the two rules rewrite into each other and each lap copies the first
/// argument in, so no term repeats. The term on the path embeds in its larger copy, and the cut ends the chain there instead of at
/// the budget (which it runs out with only the repeat cut).
#[test]
fn growing_rewrite_chains_are_cut() {
    tatic::kernel::scoped(|| {
        let rules = "lt(x, sub(y, z)) -> lt(x, add(sub(x, y), z))\nlt(x, add(y, z)) -> lt(x, sub(sub(x, y), z))\n";
        set_extra_rules(parse_rules(rules));
        RULE_BUDGET.with(|b| b.set(200));
        let cuts0 = CYCLE_CUTS.with(|c| c.get());
        let (t1, t2) = (parse_term("lt(z, add(add(x, x), y))"), parse_term("lt(z, add(y, add(x, x)))"));
        let out = rewrite_law(4, 3, &t1, &t2);
        let (cuts, left) = (CYCLE_CUTS.with(|c| c.get()) - cuts0, RULE_BUDGET.with(|b| b.get()));
        set_extra_rules(vec![]);
        RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
        println!("cuts {cuts}, budget left {left}, proved {}", out.is_some());
        assert!(cuts > 0, "no growth cut");
        assert!(left > 0, "the step budget ran out");
        if let Some((p, s)) = out {
            ck("growth law", &p, &s);
        }
    })
}

/// `RewriteMemo::filtered`: a memo built under some rules keeps its results under one more rule, tried last, for the entries whose
/// traces that rule's left side matches at no term where no rule fired; the rule miner seeds each candidate's scoring with them. The whole memo would replay
/// results the extra rule changes.
#[test]
fn filtered_memo_entries_hold_under_an_extra_rule() {
    let (n, kv) = (4, 3);
    let terms: Vec<Term> =
        ["sub(sub(z, x), sub(y, z))", "add(sub(x, y), sub(add(y, z), x))", "sub(add(x, y), sub(z, x))", "or(sub(x, y), and(sub(x, y), z))"].iter().map(|s| parse_term(s)).collect();
    let base = parse_rules("sub(add(x, y), z) -> add(sub(x, z), y)\n");
    // every term rewritten under `rules` with `memo` in force: the normal forms, the steps used, and the memo afterwards
    let run = |rules: &[(Term, Term)], memo: RewriteMemo| {
        set_extra_rules(rules.to_vec());
        REWRITE_MEMO.with(|m| *m.borrow_mut() = Some(memo));
        RULE_TRACE.with(|t| *t.borrow_mut() = Some(vec![]));
        let out: Vec<(String, i64)> = terms
            .iter()
            .map(|t| {
                RULE_BUDGET.with(|b| b.set(200));
                (rewrite(t, n, kv).0.show(), 200 - RULE_BUDGET.with(|b| b.get()))
            })
            .collect();
        RULE_TRACE.with(|t| *t.borrow_mut() = None);
        set_extra_rules(vec![]);
        RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
        (out, REWRITE_MEMO.with(|m| m.borrow_mut().take()).unwrap())
    };
    let (before, memo) = run(&base, RewriteMemo::new(kv));
    for extra in ["sub(sub(x, y), z) -> sub(x, add(y, z))\n", "or(x, and(x, y)) -> x\n"] {
        let rules: Vec<(Term, Term)> = base.iter().cloned().chain(parse_rules(extra)).collect();
        let l = &rules.last().unwrap().0;
        let seed = memo.filtered(|tr| !tr.iter().any(|(t, fired)| matches(l, t) && fired.preempted_by(|f| run_order(l, &rules.last().unwrap().1) < run_order(&f.0, &f.1))));
        assert!(!seed.map.is_empty() && seed.map.len() < memo.map.len(), "{extra}: the filter kept {} of {}", seed.map.len(), memo.map.len());
        let fresh = run(&rules, RewriteMemo::new(kv)).0;
        assert_eq!(run(&rules, seed).0, fresh, "{extra}");
        // the unfiltered memo would replay `before` (debug builds reject such a replay, `check_replay`)
        assert_ne!(before, fresh, "{extra}: the extra rule changes nothing here");
    }
}

/// A memo hit gives what a fresh rewrite would, also under rules that cycle: an entry made where the path was short is replayed
/// inside a call that a fresh rewrite would cut (docs/tier-cycle.md, the law 168 entry under Open).
#[test]
fn memo_hits_match_fresh_rewrites_under_cycling_rules() {
    let (n, kv) = (4, 3);
    // t = lt(x, sub(y, z)) -> u = lt(x, add(y, z)) -> v = lt(x, or(sub(y, z), y)) -> lt(x, and(..)): t embeds in v, so rewriting t
    // cuts at v, while u on its own (rewritten first, into the memo) does not
    let terms: Vec<Term> = ["lt(x, add(y, z))", "lt(x, sub(y, z))"].iter().map(|s| parse_term(s)).collect();
    let rules = "lt(x, sub(y, z)) -> lt(x, add(y, z))\nlt(x, add(y, z)) -> lt(x, or(sub(y, z), y))\nlt(x, or(y, z)) -> lt(x, and(y, z))\n";
    set_extra_rules(parse_rules(rules));
    let run = |memo: Option<RewriteMemo>| {
        REWRITE_MEMO.with(|m| *m.borrow_mut() = memo);
        let out: Vec<(String, i64)> = terms
            .iter()
            .map(|t| {
                RULE_BUDGET.with(|b| b.set(200));
                (rewrite(t, n, kv).0.show(), 200 - RULE_BUDGET.with(|b| b.get()))
            })
            .collect();
        REWRITE_MEMO.with(|m| m.borrow_mut().take());
        out
    };
    let (fresh, memo) = (run(None), run(Some(RewriteMemo::new(kv))));
    set_extra_rules(vec![]);
    RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
    let differ: Vec<_> = terms.iter().zip(fresh.iter().zip(&memo)).filter(|(_, (f, m))| f != m).map(|(t, (f, m))| format!("{}: fresh {f:?} memo {m:?}", t.show())).collect();
    assert!(differ.is_empty(), "{} of {} differ:\n{}", differ.len(), terms.len(), differ.join("\n"));
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

/// Check time of one rule's law alone: rule `LAW_RULE` (default 33) of the cmp3d own-rules file at `LAW_N` bits
/// (default 8), `LAW_REPS` times (default 5) after one warm-up. Each rep builds the proof and checks it in its own
/// `scoped`, one region, and times only the check. Prints `LAWT rule=.. n=.. reps=.. min=.. med=..`. The id arena's
/// A/B harness (plan docs/superpowers/plans/2026-10-14-id-arena-stage3.md; `scripts/law_ab.sh`).
#[test]
#[ignore]
pub fn law_time() {
    let env = |k: &str, d: usize| std::env::var(k).map_or(d, |v| v.parse().unwrap());
    let (i, n, reps) = (env("LAW_RULE", 33), env("LAW_N", 8), env("LAW_REPS", 5).max(1));
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/docs/runs/2026-10-12/scripts/cmp3d_own_rules.txt");
    let rules = parse_rules(&std::fs::read_to_string(path).unwrap());
    let (l, r) = &rules[i];
    let k = l.max_var().max(r.max_var()) + 1;
    let once = || {
        tatic::kernel::scoped(|| {
            let (lp, ls) = prove_rule(n, k, l, r).expect("the rule proves");
            let (p, lemmas) = PARAMS.with(|c| c.borrow_mut().take()).unwrap_or_else(|| (Postulates::new(), Vec::new()));
            let t = Instant::now();
            let ok = p.check_open(&lp, &ls);
            let took = t.elapsed();
            PARAMS.with(|c| *c.borrow_mut() = Some((p, lemmas)));
            ok.expect("the law checks");
            took
        })
    };
    once();
    let mut ts: Vec<_> = (0..reps).map(|_| once()).collect();
    ts.sort();
    println!("LAWT rule={i} n={n} reps={reps} min={:?} med={:?}", ts[0], ts[reps / 2]);
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
fn tree_step_index_matches_scan() {
    // `tree_step` as it was before `tree_candidates`: every candidate tried in order
    for (n, k) in [(3, 1), (4, 2), (8, 2), (4, 3)] {
        let cands: Vec<Term> = [Term::ZERO, Term::ONES]
            .into_iter()
            .chain((0..k).map(Term::v))
            .chain(terms(k, false).iter().copied().filter(|c| matches!(*c.node(), Node::Op(o, ..) if (1..=3).contains(&o))))
            .collect();
        let (mut found, mut tried) = (0, 0);
        for t1 in terms(k, true).iter().step_by(5) {
            let scan = cands.iter().copied().find(|c| crate::machine::tree_encoding(n, k, t1, c).is_some());
            assert!(tree_step(n, t1, k).map(|r| r.0) == scan, "n={n} {}", t1.show());
            tried += 1;
            found += scan.is_some() as usize;
        }
        assert!(found > 0 && found < tried, "n={n} k={k}: {found} of {tried}");
    }
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
