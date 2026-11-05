use super::*;

/// How `ValueMemo` stores a value: one byte for exhaustive signatures (width at most 8), `u128` for the screen.
pub trait Word: Copy + Eq + std::hash::Hash {
    fn of(x: u128) -> Self;
    fn get(self) -> u128;
    /// The operator's function on this type.
    fn pick(w: &Words) -> fn(Self, Self, Self) -> Self;
}

impl Word for u8 {
    fn of(x: u128) -> u8 {
        x as u8
    }
    fn get(self) -> u128 {
        self as u128
    }
    #[inline(always)]
    fn pick(w: &Words) -> fn(u8, u8, u8) -> u8 {
        w.w8
    }
}

impl Word for u128 {
    fn of(x: u128) -> u128 {
        x
    }
    fn get(self) -> u128 {
        self
    }
    #[inline(always)]
    fn pick(w: &Words) -> fn(u128, u128, u128) -> u128 {
        w.w128
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
    pub(super) vars: std::sync::Arc<[Box<[W]>]>,
    /// Each term's vector's id: vector `id` is the `id % per`-th of block `id / per`.
    ids: hashbrown::HashMap<Term, usize>,
    /// Vectors per block.
    per: usize,
    blocks: Vec<Vec<W>>,
    /// Value classes, made when asked (`class`): the first vector asked about with each list of values, by its hash.
    classes: hashbrown::HashTable<(u64, usize)>,
    /// `class_of[id]`: vector `id`'s class, `u32::MAX` until asked.
    class_of: Vec<u32>,
    hasher: hashbrown::DefaultHashBuilder,
}

/// `out[i] = op(x[i], y[i])` for operator `O`: its function for `W` is a constant here, so it inlines into the loop (called
/// through the pointer per element it was about 4% of a sweep, docs/tier-cycle.md, "Profile at a7b0719"), and the `u8`
/// loops work on byte lanes ("`zip_word` on native bytes").
fn zip_word<W: Word, const O: usize>(out: &mut [std::mem::MaybeUninit<W>], x: &[W], y: &[W], mask: u128) {
    let (op, mask) = (W::pick(const { &OP_INFO[O].words }), W::of(mask));
    for ((o, x), y) in out.iter_mut().zip(x).zip(y) {
        o.write(op(*x, *y, mask));
    }
}

/// `out[i] = op(x[i], y[i])` for operator `o` at one width's `mask`.
pub fn zip_op<W: Word>(o: usize, out: &mut [W], x: &[W], y: &[W], mask: u128) {
    // SAFETY: `fill_op` writes only initialized values, so `out` stays initialized
    fill_op(o, unsafe { &mut *(out as *mut [W] as *mut [std::mem::MaybeUninit<W>]) }, x, y, mask);
}

/// `zip_op` into cells that may start uninitialized: `zip_word` picked once per call. It writes every cell of `out`.
fn fill_op<W: Word>(o: usize, out: &mut [std::mem::MaybeUninit<W>], x: &[W], y: &[W], mask: u128) {
    assert!(x.len() == out.len() && y.len() == out.len(), "zip inputs of lengths {} and {} into {}", x.len(), y.len(), out.len());
    let zips: [fn(&mut [std::mem::MaybeUninit<W>], &[W], &[W], u128); OP_INFO.len()] =
        [zip_word::<W, 0>, zip_word::<W, 1>, zip_word::<W, 2>, zip_word::<W, 3>, zip_word::<W, 4>, zip_word::<W, 5>, zip_word::<W, 6>, zip_word::<W, 7>];
    zips[o](out, x, y, mask);
}

/// A `ValueMemo` block's size in bytes (one vector when a vector is larger).
const VALUE_BLOCK: usize = 1 << 16;

/// The screen's input count: all zeros, all ones, then 202 pseudo-random tuples.
pub(crate) const SCREEN_INPUTS: usize = 204;

/// The plausibility screen's value memos, by width and variable count, shared by a process's threads behind one lock: per
/// thread, 66% of a sweep's screen fills redid another thread's (docs/tier-cycle.md, "Per-thread refills"). Pure: values on
/// fixed pseudo-random inputs.
static SCREENS: crate::task::SharedMemo<(usize, usize), ValueMemo<u128>> = crate::task::SharedMemo::new();

/// `f` on the screen's value memo for width `n` and `k` variables.
pub(crate) fn with_screen<R>(n: usize, k: usize, f: impl FnOnce(&mut ValueMemo<u128>) -> R) -> R {
    SCREENS.with((n, k), || ValueMemo::screen(n, k), f)
}

impl<W: Word> ValueMemo<W> {
    pub fn new(n: usize, len: usize, vars: std::sync::Arc<[Box<[W]>]>) -> Self {
        // `fill` copies these into blocks of whole `len`-long vectors, and writes an operator's vector after them
        if let Some(v) = vars.iter().find(|v| v.len() != len) {
            panic!("variable vector of length {}, not {len}", v.len());
        }
        let per = (VALUE_BLOCK / (len * std::mem::size_of::<W>())).max(1);
        let (classes, class_of, hasher) = Default::default();
        ValueMemo { mask: low_bits(n), len, vars, ids: Default::default(), per, blocks: vec![], classes, class_of, hasher }
    }

    /// `t`'s values, one per input.
    pub fn values(&mut self, t: &Term) -> &[W] {
        let id = self.fill(*t);
        self.vector(id)
    }

    /// `t`'s value class: the id of the first vector asked about with `t`'s values, so two terms share a class exactly
    /// when they agree on every input. Grouping terms by class keys on an integer; copying each 4096-byte vector into its
    /// key was 11-13% of a stream's build (docs/tier-cycle.md, "Grouping the streams' terms, and the 2-growth build inside
    /// the 4-growth one").
    pub fn class(&mut self, t: &Term) -> u32 {
        use std::hash::BuildHasher;
        let id = self.fill(*t);
        let ValueMemo { len, per, blocks, classes, class_of, hasher, .. } = self;
        if id >= class_of.len() {
            class_of.resize(id + 1, u32::MAX);
        }
        if class_of[id] == u32::MAX {
            let at = |id: usize| -> &[W] { &blocks[id / *per][id % *per * *len..][..*len] };
            let hash = hasher.hash_one(at(id));
            let &(_, first) = classes.entry(hash, |&(_, c)| at(c) == at(id), |&(h, _)| h).or_insert((hash, id)).get();
            class_of[id] = u32::try_from(first).unwrap();
        }
        class_of[id]
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
                // the children's vectors sit in earlier blocks or earlier in the last one
                let (done, tail) = self.blocks.split_at_mut(last);
                let block = &mut tail[0];
                let base = block.as_mut_ptr();
                // SAFETY: the block was made with capacity `per * len` and is not full, so cells `off..off + len` are
                // its spare capacity: disjoint from its first `off` cells (`before`) and from the other blocks; `fill_op`
                // writes all `len` of them before `set_len` covers them.
                let (before, out) = unsafe {
                    (std::slice::from_raw_parts(base, off), std::slice::from_raw_parts_mut(base.add(off).cast(), len))
                };
                let at = |id: usize| -> &[W] {
                    let block: &[W] = if id / per == last { before } else { &done[id / per] };
                    &block[id % per * len..][..len]
                };
                fill_op(o, out, at(a), at(b), mask);
                unsafe { block.set_len(off + len) };
            }
        }
        self.ids.insert(t, id);
        id
    }

    /// The first of the first `tries` inputs on which `a` and `b` differ. The vectors are compared whole first (a
    /// `memcmp`, which stops near a difference), and scanned for the input only when they differ.
    pub fn first_difference(&mut self, a: &Term, b: &Term, tries: usize) -> Option<usize> {
        assert!(tries <= self.len, "{tries} tries over {} inputs", self.len);
        let (a, b) = (self.fill(*a), self.fill(*b));
        let (x, y) = (&self.vector(a)[..tries], &self.vector(b)[..tries]);
        if x == y {
            return None;
        }
        x.iter().zip(y).position(|(p, q)| p != q)
    }

    /// Whether `a` and `b` agree on every input.
    pub fn agree(&mut self, a: &Term, b: &Term) -> bool {
        self.first_difference(a, b, self.len).is_none()
    }

    /// Input `i`, one value per variable.
    pub fn input(&self, i: usize) -> Vec<u128> {
        self.vars.iter().map(|c| c[i].get()).collect()
    }
}

/// `exhaustive`'s inputs by width and variable count, built once per process: `bitwise_holds` asks for up to five widths
/// on every call (docs/tier-cycle.md, "F3 landed").
static EXHAUSTIVE_INPUTS: crate::task::SharedMemo<(usize, usize), std::sync::Arc<[Box<[u8]>]>> = crate::task::SharedMemo::new();

impl ValueMemo<u8> {
    /// Every width-`n` input over `nv` variables (variable `v` is bits `n*v..` of the input's index), one byte per value.
    pub fn exhaustive(n: usize, nv: usize) -> Self {
        assert!(n <= 8, "exhaustive values hold one byte per input");
        let len = 1usize << (n * nv);
        let build = || (0..nv).map(|v| (0..len).map(|i| (i >> (n * v) & low_bits(n) as usize) as u8).collect()).collect();
        ValueMemo::new(n, len, EXHAUSTIVE_INPUTS.with((n, nv), build, |vars| vars.clone()))
    }
}

/// Whether `a` and `b` agree on every input over `k` variables at widths 1..=5, narrowest first. For add-free terms
/// (bitwise operators and shifts) a position reads only a few neighbours, so these widths hold every case; `verdict`'s
/// `Bitwise` replacements and `prove_eq`'s per-position step rest on it (the kernel checks the proof regardless). Whole
/// value vectors per width: a recursive `interp` pair per input was a quarter of a sweep's samples in `verdict` alone
/// (docs/tier-cycle.md, "One exhaustive check for both").
pub fn bitwise_holds(a: &Term, b: &Term, k: usize) -> bool {
    (1..=5).all(|w| ValueMemo::exhaustive(w, k).agree(a, b))
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

/// Leaves, each of `add`, `and`, `or` and `xor` applied to two leaves, and (with `deep`) each applied to such a term and a
/// leaf, in either order.
pub(super) fn terms(nvars: usize, deep: bool) -> Vec<Term> {
    let mut leaves: Vec<Term> = (0..nvars).map(Term::v).collect();
    leaves.push(Term::ZERO);
    leaves.push(Term::ONES);
    let mut level1 = vec![];
    for o in 0..4 {
        for a in &leaves {
            for b in &leaves {
                level1.push(Term::op(o, *a, *b));
            }
        }
    }
    let mut all = leaves.clone();
    all.extend(level1.clone());
    if deep {
        for o in 0..4 {
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

