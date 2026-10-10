use super::*;

#[derive(Clone)]
pub enum Term {
    V(usize),
    Zero,
    Ones,
    Op(usize, Box<Term>, Box<Term>),
}
/// `Term::Op` indices (the position in `OP_INFO`).
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
/// Every fact about an operator, indexed as `Term::Op` (the one place that says which ops carry, are bitwise or shift).
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
/// `PERM_ORDER` (`tie`, `lpo` or unset), read once: `rule_step` is hot.
pub fn perm_order() -> &'static str {
    static P: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    P.get_or_init(|| std::env::var("PERM_ORDER").unwrap_or_default())
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
        let s = (0..n).map(|i| if i + 1 < n { a[i + 1].clone() } else { f() }).collect();
        let gs = (0..n).map(|i| if i + 1 < n { ga[i + 1].clone() } else { good_bit(false) }).collect();
        (s, gs)
    })
}
/// `(proof, type)` of `Pi x y. GoodBv x -> GoodBv y -> GoodBv (shl1 x y)`: output bit `i` is input bit `i - 1`, bit 0 false.
pub fn good_shl1(n: usize) -> (Expr, Expr) {
    good_vec(n, shl1_op(n), &move |a, _b, ga, _gb| {
        let s = (0..n).map(|i| if i == 0 { f() } else { a[i - 1].clone() }).collect();
        let gs = (0..n).map(|i| if i == 0 { good_bit(false) } else { ga[i - 1].clone() }).collect();
        (s, gs)
    })
}
/// The Church operators, indexed as `Term::Op`.
pub fn ops_for(n: usize) -> [Expr; 8] {
    [add(n), bitwise(n, &|a, b| and(a, b)), bitwise(n, &|a, b| or(a, b)), bitwise(n, &|a, b| xor(a, b)), sub(n), lt_u(n), shl1_op(n), shr1_op(n)]
}
pub const VARS: [&str; 8] = ["x", "y", "z", "u", "v", "w", "p", "q"];
impl Term {
    pub fn show(&self) -> String {
        match self {
            Term::V(i) => VARS[*i].into(),
            Term::Zero => "0".into(),
            Term::Ones => "-1".into(),
            Term::Op(o, a, b) => format!("{}({}, {})", OP_INFO[*o].name, a.show(), b.show()),
        }
    }
    /// The term as an expression, with `vals[i]` for variable `i`.
    pub fn eval(&self, ops: &[Expr], n: usize, vals: &[Expr]) -> Expr {
        match self {
            Term::V(i) => vals[*i].clone(),
            Term::Zero => lit(n, 0),
            Term::Ones => lit(n, low_bits(n)),
            Term::Op(o, a, b) => app2(ops[*o].clone(), a.eval(ops, n, vals), b.eval(ops, n, vals)),
        }
    }
    /// The value on the width-`n` operands `vals`, in plain integers (a cheap screen for false laws).
    pub fn interp(&self, n: usize, vals: &[u128]) -> u128 {
        let mask = low_bits(n);
        match self {
            Term::V(i) => vals[*i],
            Term::Zero => 0,
            Term::Ones => mask,
            Term::Op(o, a, b) => {
                let (x, y) = (a.interp(n, vals), b.interp(n, vals));
                (OP_INFO[*o].word)(x, y, mask)
            }
        }
    }
    /// Agrees on random inputs at every width 1..=6 (the plausibility screen every law passes before a machine tries it).
    pub fn is_law(&self, other: &Term, k: usize) -> bool {
        self.refute(other, k).is_none()
    }
    /// The smallest width in 1..=6 and an input tuple (over `k` variables) where the two sides differ, if the screen finds one.
    pub fn refute(&self, other: &Term, k: usize) -> Option<(usize, Vec<u128>)> {
        (1..=6).find_map(|w| self.counterexample(other, w, k).map(|vals| (w, vals)))
    }
    /// The first of the corners and 200 pseudo-random width-`n` tuples over `k` variables on which the two sides differ.
    pub fn counterexample(&self, other: &Term, n: usize, k: usize) -> Option<Vec<u128>> {
        let mask = low_bits(n);
        let mut seed = 0x9e37_79b9_7f4a_7c15u128;
        (0..204).find_map(|i| {
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
            (self.interp(n, &vals) != other.interp(n, &vals)).then_some(vals)
        })
    }
    /// Whether `self` and `other` agree on the corners and 200 pseudo-random width-`n` tuples over `k` variables.
    pub fn plausibly_equals(&self, other: &Term, n: usize, k: usize) -> bool {
        self.counterexample(other, n, k).is_none()
    }
    pub fn has_shift(&self) -> bool {
        match self {
            Term::Op(o, a, b) => OP_INFO[*o].shift || a.has_shift() || b.has_shift(),
            _ => false,
        }
    }
    /// No add, sub or lt anywhere: bitwise operators and shifts only.
    pub fn add_free(&self) -> bool {
        match self {
            Term::Op(o, a, b) => (OP_INFO[*o].bitwise || OP_INFO[*o].shift) && a.add_free() && b.add_free(),
            _ => true,
        }
    }
    pub fn uses_add(&self) -> bool {
        match self {
            Term::Op(o, a, b) => *o == ADD || *o == SUB || a.uses_add() || b.uses_add(),
            _ => false,
        }
    }
    /// Whether variable `v` occurs in the term (`show().contains(..)` would also match `xor` and `sub`).
    pub fn has_var(&self, v: usize) -> bool {
        match self {
            Term::V(i) => *i == v,
            Term::Op(_, a, b) => a.has_var(v) || b.has_var(v),
            _ => false,
        }
    }
    pub fn max_var(&self) -> usize {
        match self {
            Term::V(i) => *i,
            Term::Op(_, a, b) => a.max_var().max(b.max_var()),
            _ => 0,
        }
    }
    /// The term's value at one bit position, a `Bool0`, given the variables' bits (`bits[v]`); bitwise ops only.
    pub fn bit(&self, bits: &[Expr]) -> Expr {
        match self {
            Term::V(i) => bits[*i].clone(),
            Term::Zero => f(),
            Term::Ones => t(),
            Term::Op(o, a, b) => {
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

/// Leaves, every operator applied to two leaves, and (with `deep`) every operator applied to such a term
/// and a leaf, in either order.
pub fn terms(nvars: usize, deep: bool) -> Vec<Term> {
    let mut leaves: Vec<Term> = (0..nvars).map(Term::V).collect();
    leaves.push(Term::Zero);
    leaves.push(Term::Ones);
    let mut level1 = vec![];
    for o in 0..nops() {
        for a in &leaves {
            for b in &leaves {
                level1.push(Term::Op(o, Box::new(a.clone()), Box::new(b.clone())));
            }
        }
    }
    let mut all = leaves.clone();
    all.extend(level1.clone());
    if deep {
        for o in 0..nops() {
            for a in &level1 {
                for b in &leaves {
                    all.push(Term::Op(o, Box::new(a.clone()), Box::new(b.clone())));
                    all.push(Term::Op(o, Box::new(b.clone()), Box::new(a.clone())));
                }
            }
        }
    }
    all
}

pub type NfCache = std::collections::HashMap<(String, u128), Expr>;

/// The normal form of `t` on the input `tuple`, from the normal forms of its operands: each subterm is
/// normalized once per tuple across all terms, and the operands enter already normal.
pub fn nf_cached(t: &Term, ops: &[Expr], n: usize, tuple: u128, cache: &mut NfCache) -> Expr {
    let mask = low_bits(n);
    let Term::Op(o, a, b) = t else {
        return match t {
            Term::V(i) => lit(n, (tuple >> (n * i)) & mask),
            Term::Zero => lit(n, 0),
            _ => lit(n, mask),
        };
    };
    let key = (t.show(), tuple);
    if let Some(e) = cache.get(&key) {
        return e.clone();
    }
    let (x, y) = (nf_cached(a, ops, n, tuple, cache), nf_cached(b, ops, n, tuple, cache));
    let e = normalize(&app2(ops[*o].clone(), x, y));
    cache.insert(key, e.clone());
    e
}

pub fn fingerprint(t: &Term, ops: &[Expr], n: usize, tuples: &[u128], cache: &mut NfCache) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    for &tuple in tuples {
        format!("{:?}", nf_cached(t, ops, n, tuple, cache)).hash(&mut h);
    }
    h.finish()
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
            e.push(apps(bit_law.clone(), vs.iter().cloned().chain((0..k).map(|v| goods(v, i))).collect()));
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
        id(ty.clone(), l, r)
    };
    // the motive for eliminating vector `j` at depth `d` (inside the previous level's binders), under its own binder
    let motive = |j: usize, d: usize| {
        let args = (0..k)
            .map(|v| {
                if v < j {
                    mk(&(0..n).map(|i| shift(&at(d, level(v) + i), 0, 1)).collect::<Vec<_>>())
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
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    for n in [1usize, 2, 4] {
        for (name, t1, t2) in [
            ("and x y = and y x", op(1, v(0), v(1)), op(1, v(1), v(0))),
            ("xor x x = 0", op(3, v(0), v(0)), Term::Zero),
            ("or x -1 = -1", op(2, v(0), Term::Ones), Term::Ones),
            ("and x (or x y) = x", op(1, v(0), op(2, v(0), v(1))), v(0)),
        ] {
            let (p, s) = bitwise_law(n, &t1, &t2);
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        for (name, t1, t2) in [("and x y = or x y", op(1, v(0), v(1)), op(2, v(0), v(1))), ("xor x x = -1", op(3, v(0), v(0)), Term::Ones)] {
            let (p, s) = bitwise_law(n, &t1, &t2);
            assert!(check(&Ctx::new(), &p, &s).is_err(), "false law `{name}` must be rejected at n={n}");
        }
    }
}

// ---- Rewriting with proven lemmas (search note section 10). An `add` conjecture is simplified on both sides by
// the library lemmas `add a 0 = a`, `add 0 a = a` and `add a b = add b a` (the last used to order the operands),
// each rewrite justified by `cong_n` on the enclosing operator and chained with `trans_proof`; if the two
// results are then equal, or both add-free, `bitwise_law` closes the gap.

thread_local! {
    /// Lemmas built by `add_tree_law`, keyed on the side machine, encoding tables and lemma tag; shared across conjectures.
    pub static LEMMAS: std::cell::RefCell<std::collections::HashMap<String, Expr>> = Default::default();
    pub static CLOSED: std::cell::RefCell<std::collections::HashMap<String, (Expr, Expr)>> = Default::default();
}
/// A closed library term built once per key (the proofs and witnesses the rewriter reuses at every step).
pub fn memo(key: String, build: impl FnOnce() -> (Expr, Expr)) -> (Expr, Expr) {
    if let Some(v) = CLOSED.with(|c| c.borrow().get(&key).cloned()) {
        return v;
    }
    let v = build();
    CLOSED.with(|c| c.borrow_mut().insert(key, v.clone()));
    v
}

/// Whether the rewriter's rule `name` is switched off by the env var `ABLATE` (comma list: zero, comm, assoc, not, collapse).
pub fn ablated(name: &str) -> bool {
    std::env::var("ABLATE").is_ok_and(|v| v.split(',').any(|x| x == name))
}

/// `(value, GoodBv witness)` of `t` in context `[x, y, gx, gy]`.
pub fn witnessed(t: &Term, n: usize, goods: &[(Expr, Expr)]) -> (Expr, Expr) {
    let all = low_bits(n);
    match t {
        Term::V(i) => goods[*i].clone(),
        Term::Zero => (lit(n, 0), good_lit(n, 0)),
        Term::Ones => (lit(n, all), good_lit(n, all)),
        Term::Op(o, a, b) => {
            let ((av, aw), (bv, bw)) = (witnessed(a, n, goods), witnessed(b, n, goods));
            let (op, good_op) = match o {
                0 => (add(n), memo(format!("good_add{n}"), || good_add(n)).0),
                4 => (sub(n), memo(format!("good_sub{n}"), || good_sub(n)).0),
                6 => (shl1_op(n), memo(format!("good_shl1{n}"), || good_shl1(n)).0),
                7 => (shr1_op(n), memo(format!("good_shr1{n}"), || good_shr1(n)).0),
                _ => memo(format!("gbit{n}_{o}"), || {
                    let o = *o;
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
                    let (gp, _) = good_vec(n, vec.clone(), &move |a, b, ga, gb| {
                        let s = (0..n).map(|i| opf(a[i].clone(), b[i].clone())).collect();
                        let gs = (0..n).map(|i| apps(g.clone(), vec![a[i].clone(), b[i].clone(), ga[i].clone(), gb[i].clone()])).collect();
                        (s, gs)
                    });
                    (vec, gp)
                }),
            };
            (app2(op.clone(), av.clone(), bv.clone()), apps(good_op, vec![av, bv, aw, bw]))
        }
    }
}

/// A sum of two (atom-abstracted) bitwise operands that a constant carry reduces to 0, -1 or one of its atoms:
/// the rewritten term and the proof from `carry_chain_law` instantiated at the atoms' values and witnesses.
pub fn chain_step(n: usize, a: &Term, b: &Term, goods: &[(Expr, Expr)]) -> Option<(Term, Expr)> {
    if ablated("chain") {
        return None;
    }
    let mut atoms = vec![];
    let (a1, b1) = (abstract_atoms(a, &mut atoms, 2)?, abstract_atoms(b, &mut atoms, 2)?);
    for cand in [Term::Zero, Term::Ones, Term::V(0), Term::V(1)] {
        if matches!(cand, Term::V(i) if i >= atoms.len()) || find_constant_carry(&a1, &b1, &cand).is_none() {
            continue;
        }
        let law = carry_chain_law(n, &Term::Op(ADD, Box::new(a1.clone()), Box::new(b1.clone())), &cand)?;
        let w: Vec<(Expr, Expr)> = (0..2).map(|i| atoms.get(i).map_or(goods[0].clone(), |t| witnessed(t, n, goods))).collect();
        let proof = apps(law.0, vec![w[0].0.clone(), w[1].0.clone(), w[0].1.clone(), w[1].1.clone()]);
        let target = if let Term::V(i) = cand { atoms[i].clone() } else { cand };
        return Some((target, proof));
    }
    None
}

/// A sum tree of add-free leaves that the carry-encoding search shows equal to a constant, a variable or one
/// bitwise operation on two of them (so `-1 - x` becomes `x ^ -1`): that value and
/// the proof (`add_tree_law` at the variables' values and witnesses). Ablation name `tree`.
pub fn tree_step(n: usize, t1: &Term, goods: &[(Expr, Expr)]) -> Option<(Term, Expr)> {
    if ablated("tree") {
        return None;
    }
    let k = goods.len();
    // the constants, the variables, then every operator applied to two of them (a plain-integer screen in
    // `add_tree_law` discards the false candidates cheaply)
    for cand in [Term::Zero, Term::Ones].into_iter().chain((0..k).map(Term::V)).chain(terms(k, false).into_iter().filter(|c| matches!(c, Term::Op(o, ..) if (1..=3).contains(o)))) {
        if let Some(law) = add_tree_law(n, k, t1, &cand) {
            let args = goods.iter().map(|g| g.0.clone()).chain(goods.iter().map(|g| g.1.clone())).collect();
            return Some((cand, apps(law.0, args)));
        }
    }
    None
}

/// A library law used as a left-to-right rewrite rule: `lhs = rhs` over the pattern variables `V(0)..`, each instance
/// proved from the law `add_tree_law` proves once (per width) for the patterns themselves. `name` is the `ABLATE` key.
pub struct Rule {
    pub name: &'static str,
    pub lhs: Term,
    pub rhs: Term,
}

thread_local! {
    /// Set by the rule miner while scoring (`RULEMINER_FAST=1`): `prove_eq` counts a machine fallback without building its proof
    /// (the returned proof is a placeholder, never checked).
    pub static SCORE_ONLY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Rules added at run time (by the rule miner), after the built-in ones.
    pub static EXTRA_RULES: std::cell::RefCell<Vec<(Term, Term)>> = Default::default();
    /// While `Some`, `rule_step` records every term it is asked to rewrite: a rule added at the end of the rule list can change a
    /// rewriting only if its left side matches one of them.
    pub static RULE_TRACE: std::cell::RefCell<Option<Vec<Term>>> = const { std::cell::RefCell::new(None) };
}
// How many more rule applications `rule_step` may make; the rule miner sets it per trial so that a candidate that
// undoes a built-in rule cannot loop. Soundness is unaffected: a refused step only leaves the term less normalized.
thread_local! {
    pub static RULE_BUDGET: std::cell::Cell<i64> = const { std::cell::Cell::new(i64::MAX / 2) };
    /// Rules (`lhs -> rhs`) being proved by `prove_rule` through the rewriter; `rule_step` skips them.
    pub static PROVING: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
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
        parse_rules(&text)
    })
}

pub fn rules() -> Vec<Rule> {
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let v = Term::V;
    let shl = |a: Term| Term::Op(SHL1, Box::new(a), Box::new(Term::Zero));
    let shr = |a: Term| Term::Op(SHR1, Box::new(a), Box::new(Term::Zero));
    let lt = |a: Term, b: Term| Term::Op(LT, Box::new(a), Box::new(b));
    let mut all = vec![
        Rule { name: "shldist", lhs: shl(op(0, v(0), v(1))), rhs: op(0, shl(v(0)), shl(v(1))) },
        Rule { name: "shldistsub", lhs: shl(op(4, v(0), v(1))), rhs: op(4, shl(v(0)), shl(v(1))) },
        Rule { name: "shldistand", lhs: shl(op(1, v(0), v(1))), rhs: op(1, shl(v(0)), shl(v(1))) },
        Rule { name: "shldistor", lhs: shl(op(2, v(0), v(1))), rhs: op(2, shl(v(0)), shl(v(1))) },
        Rule { name: "shldistxor", lhs: shl(op(3, v(0), v(1))), rhs: op(3, shl(v(0)), shl(v(1))) },
        Rule { name: "notsub", lhs: op(3, v(0), Term::Ones), rhs: op(4, Term::Ones, v(0)) },
        Rule { name: "notsubl", lhs: op(3, Term::Ones, v(0)), rhs: op(4, Term::Ones, v(0)) },
        // lt is false when the right side is 0, the left side is -1, or the sides are equal (mined, section 43)
        Rule { name: "ltself", lhs: lt(v(0), v(0)), rhs: lt(Term::Ones, Term::Ones) },
        Rule { name: "ltzero", lhs: lt(v(0), Term::Zero), rhs: lt(Term::Ones, Term::Ones) },
        Rule { name: "ltmax", lhs: lt(Term::Ones, v(0)), rhs: lt(Term::Ones, Term::Ones) },
        Rule { name: "shrzero", lhs: shr(Term::Zero), rhs: Term::Zero },
        Rule { name: "shrdistand", lhs: shr(op(1, v(0), v(1))), rhs: op(1, shr(v(0)), shr(v(1))) },
        Rule { name: "shrdistor", lhs: shr(op(2, v(0), v(1))), rhs: op(2, shr(v(0)), shr(v(1))) },
        Rule { name: "shrdistxor", lhs: shr(op(3, v(0), v(1))), rhs: op(3, shr(v(0)), shr(v(1))) },
        Rule { name: "shrnot", lhs: shrnot_rule().0, rhs: shrnot_rule().1 },
        Rule { name: "shlzero", lhs: shl(Term::Zero), rhs: Term::Zero },
        Rule { name: "double", lhs: op(0, v(0), v(0)), rhs: shl(v(0)) },
        Rule { name: "doublechain", lhs: op(0, v(0), op(0, v(0), v(1))), rhs: op(0, shl(v(0)), v(1)) },
        // mined by `rule_miner` (section 36): cancellation
        Rule { name: "cancelr", lhs: op(4, op(0, v(0), v(1)), v(1)), rhs: v(0) },
        Rule { name: "cancell", lhs: op(4, op(0, v(0), v(1)), v(0)), rhs: v(1) },
        Rule { name: "subdist", lhs: op(4, op(0, v(0), v(1)), op(0, v(2), v(3))), rhs: op(0, op(4, v(0), v(2)), op(4, v(1), v(3))) },
    ];
    all.extend(promoted_rules().iter().map(|(l, r)| Rule { name: "promoted", lhs: l.clone(), rhs: r.clone() }));
    all.extend(rule_set().iter().map(|(l, r)| Rule { name: "ruleset", lhs: l.clone(), rhs: r.clone() }));
    EXTRA_RULES.with(|e| all.extend(e.borrow().iter().map(|(l, r)| Rule { name: "mined", lhs: l.clone(), rhs: r.clone() })));
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

/// The rules of a rule file: one `lhs -> rhs` per line, other lines ignored.
pub fn parse_rules(text: &str) -> Vec<(Term, Term)> {
    text.lines().filter_map(|l| l.split_once(" -> ")).map(|(a, b)| (parse_term(a), parse_term(b))).collect()
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
            return Term::Op(o, Box::new(a), Box::new(b));
        }
        match name {
            "0" => Term::Zero,
            "-1" => Term::Ones,
            _ => Term::V(VARS.iter().position(|v| *v == name).unwrap_or_else(|| panic!("unknown leaf {name}"))),
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
    /// Number of nodes.
    pub fn size(&self) -> usize {
        match self {
            Term::Op(_, a, b) => 1 + a.size() + b.size(),
            _ => 1,
        }
    }
    /// Occurrences of each variable (`out[v]`).
    pub fn occurrences(&self, out: &mut [usize; 8]) {
        match self {
            Term::V(v) => out[*v] += 1,
            Term::Op(_, a, b) => {
                a.occurrences(out);
                b.occurrences(out);
            }
            _ => {}
        }
    }
    /// All subterms (with repeats), the term itself first.
    pub fn subterms(&self, out: &mut Vec<Term>) {
        out.push(self.clone());
        if let Term::Op(_, a, b) = self {
            a.subterms(out);
            b.subterms(out);
        }
    }
}

/// `shr1(sub(-1, x)) -> xor(shr1(x), shr1(-1))`: a shift of a bitwise not (`sub(-1, x)` is what `notsub` makes of
/// `xor(x, -1)`) distributes like the other bitwise operators; without it the not blocks `shrdistxor`.
pub fn shrnot_rule() -> (Term, Term) {
    let b = |o: usize, x: Term, y: Term| Term::Op(o, Box::new(x), Box::new(y));
    let shr = |x: Term| b(SHR1, x, Term::Zero);
    (shr(b(SUB, Term::Ones, Term::V(0))), b(XOR, shr(Term::V(0)), shr(Term::Ones)))
}

/// Proof of the `shrnot` rule through the middle term `shr1(xor(x, -1))`: the rewriter proves it equal to the left side
/// (with `notsub` on) and to the right side (with `notsub` off, so `shrdistxor` sees the xor), neither using `shrnot`.
pub fn shr_not_law(n: usize) -> Option<(Expr, Expr)> {
    let b = |o: usize, x: Term, y: Term| Term::Op(o, Box::new(x), Box::new(y));
    let (l, r) = shrnot_rule();
    let m = b(SHR1, b(XOR, Term::V(0), Term::Ones), Term::Zero);
    let key = |(lhs, rhs): (&Term, &Term)| format!("{} -> {}", lhs.show(), rhs.show());
    let own = key((&l, &r));
    let notsub = rules().into_iter().find(|x| x.name == "notsub").map(|x| key((&x.lhs, &x.rhs)))?;
    let prove = |blocked: &[String], t1: &Term, t2: &Term| {
        let outer = PROVING.with(|p| p.borrow().len());
        PROVING.with(|p| p.borrow_mut().extend(blocked.iter().cloned()));
        let out = rewrite_law(n, 1, t1, t2);
        PROVING.with(|p| p.borrow_mut().truncate(outer));
        out
    };
    let to_left = prove(std::slice::from_ref(&own), &m, &l)?;
    let to_right = prove(&[own, notsub], &m, &r)?;
    let (ops, bv) = (ops_for(n), bv_ty(n));
    let vals = vec![var(1)];
    let ev = |t: &Term| t.eval(&ops, n, &vals);
    let args = vec![var(1), var(0)];
    let (p1, p2) = (apps(to_left.0, args.clone()), apps(to_right.0, args));
    let body = trans_proof(&bv, &ev(&l), &ev(&m), &ev(&r), sym(&bv, &ev(&m), &ev(&l), p1), p2);
    let g = app(good_bv(n), var(0));
    let stmt = pi(g.clone(), id(bv.clone(), ev(&l), ev(&r)));
    Some((lam(bv.clone(), lam(g, body)), pi(bv, stmt)))
}

/// The law behind a rule: bitwise/shift rules by the per-position prover, the rest by the carry machines.
pub fn prove_rule(n: usize, k: usize, l: &Term, r: &Term) -> Option<(Expr, Expr)> {
    if (l.show(), r.show()) == (shrnot_rule().0.show(), shrnot_rule().1.show()) {
        shr_not_law(n)
    } else if l.add_free() && r.add_free() {
        let law = bitwise_law_k(n, k, l, r);
        check(&Ctx::new(), &law.0, &law.1).ok().map(|_| law)
    } else if matches!(l, Term::Op(SHR1, ..)) && matches!(r, Term::Op(SHR1, ..) | Term::Zero) || matches!(r, Term::Op(SHR1, ..)) && matches!(l, Term::Zero) {
        // laws with a `shr1` root are not machines: prove them with the rewriter (which falls back on the bit-0 mask
        // reduction), without the rule being proved, so that it cannot be used in its own proof
        let key = format!("{} -> {}", l.show(), r.show());
        PROVING.with(|p| p.borrow_mut().push(key));
        let saved = RULE_BUDGET.with(|b| b.replace(10_000));
        let out = rewrite_law(n, k, l, r);
        RULE_BUDGET.with(|b| b.set(saved));
        PROVING.with(|p| p.borrow_mut().pop());
        out
    } else {
        add_tree_law(n, k, l, r)
    }
}

/// The rule order's weight of a term, a polynomial interpretation `c + sum_v a_v * x_v` (`x_v >= 1` is the weight of
/// whatever replaces variable `v`): leaves 1, `shl1`/`shr1` double (`2x`, so distributing a shift over an operator goes
/// down), every other operator `x + y + 1`.
pub fn rule_weight(t: &Term) -> (i64, [i64; 8]) {
    match t {
        Term::V(v) => {
            let mut a = [0; 8];
            a[*v] = 1;
            (0, a)
        }
        Term::Zero | Term::Ones => (1, [0; 8]),
        Term::Op(SHL1 | SHR1, x, _) => {
            let (c, mut a) = rule_weight(x);
            a.iter_mut().for_each(|k| *k *= 2);
            (2 * c, a)
        }
        Term::Op(_, x, y) => {
            let ((c1, a1), (c2, a2)) = (rule_weight(x), rule_weight(y));
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
    match (l, r) {
        (Term::Op(lo, la, lb), Term::Op(ro, ra, rb)) => {
            if lo != ro {
                return OP_INFO[*lo].prec > OP_INFO[*ro].prec;
            }
            for (a, b) in [(la, ra), (lb, rb)] {
                if a.show() != b.show() {
                    return a.size() > b.size() || (a.size() == b.size() && tie_greater(a, b));
                }
            }
            false
        }
        (Term::Op(..), _) => true,
        _ => false,
    }
}

/// Rank of a leaf or head in the lexicographic path order below: leaves under all operators, operators by `OpInfo::prec`
/// and then index, so the precedence is total.
fn lpo_rank(t: &Term) -> (i32, i64) {
    match t {
        Term::Zero => (-3, 0),
        Term::Ones => (-2, 0),
        Term::V(i) => (-1, *i as i64),
        Term::Op(o, ..) => (OP_INFO[*o].prec, *o as i64),
    }
}

/// `s > t` in the lexicographic path order with the total precedence of `lpo_rank` (`PERM_ORDER=lpo`, section 89). It is
/// a reduction order (well-founded, closed under contexts) and total on terms, so an instance that goes down in it
/// cannot be rewritten back, whatever the surrounding term; `show()` comparison of an instance is not closed under contexts.
pub fn lpo_greater(s: &Term, t: &Term) -> bool {
    let Term::Op(_, sa, sb) = s else {
        return !matches!(t, Term::Op(..)) && lpo_rank(s) > lpo_rank(t);
    };
    if [sa, sb].into_iter().any(|x| x.show() == t.show() || lpo_greater(x, t)) {
        return true;
    }
    let Term::Op(_, ta, tb) = t else { return true };
    let (rs, rt) = (lpo_rank(s), lpo_rank(t));
    if rs > rt {
        return lpo_greater(s, ta) && lpo_greater(s, tb);
    }
    if rs < rt {
        return false;
    }
    if sa.show() != ta.show() {
        lpo_greater(sa, ta) && lpo_greater(s, tb)
    } else {
        lpo_greater(sb, tb)
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
    // `PERM_ORDER=lpo` (section 89): `rule_step` orients every tied rule instance by instance, so both directions are admissible
    let lpo = perm_order() == "lpo";
    rule_order_ok(l, r) || (rule_tied(l, r) && (lpo || tie_greater(l, r) || rule_permutative(l, r)))
}

pub fn match_pat(p: &Term, t: &Term, sub: &mut Vec<Option<Term>>) -> bool {
    match (p, t) {
        (Term::V(i), _) => match &sub[*i] {
            Some(b) => b.show() == t.show(),
            None => {
                sub[*i] = Some(t.clone());
                true
            }
        },
        (Term::Zero, Term::Zero) | (Term::Ones, Term::Ones) => true,
        (Term::Op(o, a, b), Term::Op(o2, c, d)) => o == o2 && match_pat(a, c, sub) && match_pat(b, d, sub),
        _ => false,
    }
}

pub fn subst_pat(p: &Term, sub: &[Option<Term>]) -> Term {
    match p {
        Term::V(i) => sub[*i].clone().expect("bound"),
        Term::Op(o, a, b) => Term::Op(*o, Box::new(subst_pat(a, sub)), Box::new(subst_pat(b, sub))),
        _ => p.clone(),
    }
}

/// Print every rule application (set by the `normal_forms` debug test).
pub static TRACE_RULES: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Instances of `rule_step` by rule name, for the audit.
pub static RULE_HITS: std::sync::Mutex<Vec<(&'static str, u64)>> = std::sync::Mutex::new(Vec::new());

/// Constant folding (`ABLATE=fold`): a closed term equal at widths 1-6 to `0`, `-1` or `1` (written `sub(0, -1)`, the
/// library has no literal `1`), without `shr1`, is a rule `t -> constant`, proved like any other rule.
pub fn fold_rule(t: &Term) -> Option<Rule> {
    fn closed(t: &Term) -> bool {
        match t {
            Term::V(_) | Term::Op(SHR1, ..) => false, // `shr1` is not a machine: `prove_rule` cannot prove laws over it
            Term::Op(_, a, b) => closed(a) && closed(b),
            _ => true,
        }
    }
    let one = Term::Op(SUB, Box::new(Term::Zero), Box::new(Term::Ones));
    if !matches!(t, Term::Op(o, ..) if *o != LT) || ablated("fold") || t.show() == one.show() || !closed(t) {
        return None;
    }
    [Term::Zero, Term::Ones, one].into_iter().find(|c| t.is_law(c, 1)).map(|c| Rule { name: "fold", lhs: t.clone(), rhs: c })
}

/// The first library rule (not ablated) whose left side matches `t`: the rewritten term and the proof.
pub fn rule_step(n: usize, t: &Term, goods: &[(Expr, Expr)]) -> Option<(Term, Expr)> {
    RULE_TRACE.with(|tr| {
        if let Some(v) = tr.borrow_mut().as_mut() {
            v.push(t.clone());
        }
    });
    for r in fold_rule(t).into_iter().chain(rules()) {
        let k = r.lhs.max_var().max(r.rhs.max_var()) + 1;
        let mut sub = vec![None; k];
        if ablated(r.name) || !match_pat(&r.lhs, t, &mut sub) {
            continue;
        }
        if PROVING.with(|p| !p.borrow().is_empty() && p.borrow().contains(&format!("{} -> {}", r.lhs.show(), r.rhs.show()))) {
            continue;
        }
        // a rule whose right side is an instance of its own left side (`lt(x,x) -> lt(-1,-1)`) must not rewrite its result
        if subst_pat(&r.rhs, &sub.iter().map(|s| s.clone().or(Some(Term::Zero))).collect::<Vec<_>>()).show() == t.show() {
            continue;
        }
        if TRACE_RULES.load(std::sync::atomic::Ordering::Relaxed) {
            println!("TRACE {} -> {}   on {}", r.lhs.show(), r.rhs.show(), t.show());
        }
        // a permutative rule (ordered rewriting): only when the instance goes down in the order on `show()` strings
        let lpo = perm_order() == "lpo";
        if lpo && rule_tied(&r.lhs, &r.rhs) && !rule_order_ok(&r.lhs, &r.rhs) {
            // every rule that ties in the weight order must go down in the path order, instance by instance
            let inst = subst_pat(&r.rhs, &sub.iter().map(|s| s.clone().or(Some(Term::Zero))).collect::<Vec<_>>());
            if !lpo_greater(t, &inst) {
                continue;
            }
        } else if rule_permutative(&r.lhs, &r.rhs) {
            let inst = subst_pat(&r.rhs, &sub.iter().map(|s| s.clone().or(Some(Term::Zero))).collect::<Vec<_>>());
            // `PERM_ORDER=tie` (section 87): the instance must go down in the tie-break order of the other rules, and only
            // when that order does not separate the two terms does `show()` decide; by default `show()` alone
            let down = if perm_order() == "tie" {
                tie_greater(t, &inst) || (!tie_greater(&inst, t) && inst.show() < t.show())
            } else {
                inst.show() < t.show()
            };
            if !down {
                continue;
            }
        }
        if RULE_BUDGET.with(|b| b.replace(b.get() - 1)) <= 0 {
            return None;
        }
        let law = memo(format!("rule_{}_{}_{}_{n}", r.name, r.lhs.show(), r.rhs.show()), || prove_rule(n, k, &r.lhs, &r.rhs).unwrap_or_else(|| panic!("rule {} is not provable", r.name)));
        // a pattern variable the left side does not mention is free in the law: any value serves
        let w: Vec<(Expr, Expr)> = sub.iter().map(|s| s.as_ref().map_or(goods[0].clone(), |t| witnessed(t, n, goods))).collect();
        let args = w.iter().map(|x| x.0.clone()).chain(w.iter().map(|x| x.1.clone())).collect();
        let mut hits = RULE_HITS.lock().unwrap();
        match hits.iter_mut().find(|h| h.0 == r.name) {
            Some(h) => h.1 += 1,
            None => hits.push((r.name, 1)),
        }
        return Some((subst_pat(&r.rhs, &sub), apps(law.0, args)));
    }
    None
}

/// `t` rewritten bottom-up, with a proof of `Id(Bv_n, t, t')` in context `[x, y, gx, gy]`.
pub fn rewrite(t: &Term, n: usize, ops: &[Expr], goods: &[(Expr, Expr)]) -> (Term, Expr) {
    let vals: Vec<Expr> = goods.iter().map(|g| g.0.clone()).collect();
    let ev = |t: &Term| t.eval(ops, n, &vals);
    let Term::Op(o, a, b) = t else { return (t.clone(), refl(ev(t))) };
    let ((a2, pa), (b2, pb)) = (rewrite(a, n, ops, goods), rewrite(b, n, ops, goods));
    // an `lt` root gives one bit, every other operator a vector
    let rt = bv_ty(if *o == LT { 1 } else { n });
    let cong = cong_n(&bv_ty(n), &rt, &ops[*o], &[ev(a), ev(b)], &[ev(&a2), ev(&b2)], vec![pa, pb]);
    let t1 = Term::Op(*o, Box::new(a2.clone()), Box::new(b2.clone()));
    if *o != ADD {
        // the library rules first (`shldist`, ...)
        if let Some((target, step)) = rule_step(n, &t1, goods) {
            let (t3, p3) = rewrite(&target, n, ops, goods);
            let first = trans_proof(&rt, &ev(t), &ev(&t1), &ev(&target), cong, step);
            return (t3.clone(), trans_proof(&rt, &ev(t), &ev(&target), &ev(&t3), first, p3));
        }
        if *o == SUB {
            // a difference: then the carry-encoding search
            return match tree_step(n, &t1, goods) {
                Some((target, law)) => (target.clone(), trans_proof(&rt, &ev(t), &ev(&t1), &ev(&target), cong, law)),
                None => (t1, cong),
            };
        }
        if matches!(*o, LT | SHL1 | SHR1) {
            return (t1, cong);
        }
        // bitwise and shift terms only: a node equal to 0, -1 or one of its own subterms collapses to it, by the
        // per-position prover (the truth-table collapse below treats a shift as an atom)
        if let (false, true, true) = (ablated("collapse"), t1.add_free(), t1.has_shift()) {
            let k = goods.len();
            let mut subs = vec![];
            t1.subterms(&mut subs);
            let cands = [Term::Zero, Term::Ones].into_iter().chain(subs.into_iter().skip(1).filter(|c| c.size() < t1.size()));
            if let Some(c) = cands.into_iter().find(|c| c.add_free() && t1.is_law(c, k)) {
                let args = goods.iter().map(|g| g.0.clone()).chain(goods.iter().map(|g| g.1.clone())).collect();
                let law = apps(bitwise_law_k(n, k, &t1, &c).0, args);
                return (c.clone(), trans_proof(&bv_ty(n), &ev(t), &ev(&t1), &ev(&c), cong, law));
            }
        }
        // a bitwise node equal to 0, -1 or one of its atoms collapses to it (truth table, then `bitwise_law`)
        let (mut atoms, k) = (vec![], goods.len());
        if let (false, Some(abs)) = (ablated("collapse"), abstract_atoms(&t1, &mut atoms, k)) {
            let truth = |t: &Term| (0..1usize << k).map(|m| normalize(&t.bit(&(0..k).map(|v| bit(m >> v & 1 == 1)).collect::<Vec<_>>()))).collect::<Vec<_>>();
            let want = truth(&abs);
            let cands: Vec<Term> = [Term::Zero, Term::Ones].into_iter().chain((0..k).map(Term::V)).collect();
            if let Some(c) = cands.iter().find(|c| c.max_var() < atoms.len().max(1) && truth(c) == want) {
                let target = if let Term::V(i) = c { atoms[*i].clone() } else { c.clone() };
                if target.show() != t1.show() {
                    let w: Vec<(Expr, Expr)> = (0..k).map(|i| atoms.get(i).map_or(goods[0].clone(), |a| witnessed(a, n, goods))).collect();
                    let args = w.iter().map(|x| x.0.clone()).chain(w.iter().map(|x| x.1.clone())).collect();
                    let law = apps(bitwise_law_k(n, k, &abs, c).0, args);
                    return (target.clone(), trans_proof(&bv_ty(n), &ev(t), &ev(&t1), &ev(&target), cong, law));
                }
            }
        }
        // commutative operands in a fixed order (constants last), by the generic bitwise law
        let key = |t: &Term| match t {
            Term::Zero => "~0".to_string(),
            Term::Ones => "~1".to_string(),
            _ => t.show(),
        };
        if key(&b2) < key(&a2) {
            let t2 = Term::Op(*o, Box::new(b2.clone()), Box::new(a2.clone()));
            let ((av, aw), (bv, bw)) = (witnessed(&a2, n, goods), witnessed(&b2, n, goods));
            let swap = |x: Term, y: Term| Term::Op(*o, Box::new(x), Box::new(y));
            let law = apps(bitwise_law(n, &swap(Term::V(0), Term::V(1)), &swap(Term::V(1), Term::V(0))).0, vec![av, bv, aw, bw]);
            return (t2.clone(), trans_proof(&bv_ty(n), &ev(t), &ev(&t1), &ev(&t2), cong, law));
        }
        return (t1, cong);
    }
    let (av, aw) = witnessed(&a2, n, goods);
    let (bv, bw) = witnessed(&b2, n, goods);
    let assoc = |p: &Term, q: &Term, r: &Term| {
        let ((pv, pw), (qv, qw), (rv, rw)) = (witnessed(p, n, goods), witnessed(q, n, goods), witnessed(r, n, goods));
        apps(memo(format!("assoc{n}"), || add_assoc_proof(n, false)).0, vec![pv, qv, rv, pw, qw, rw])
    };
    let sum = |p: &Term, q: &Term| Term::Op(ADD, Box::new(p.clone()), Box::new(q.clone()));
    let step = if !ablated("zero") && matches!(b2, Term::Zero) {
        Some((a2.clone(), app2(memo(format!("idr{n}"), || add_identity_proof(n, 0, false)).0, av, aw)))
    } else if !ablated("zero") && matches!(a2, Term::Zero) {
        Some((b2.clone(), app2(memo(format!("idl{n}"), || add_identity_proof(n, 0, true)).0, bv, bw)))
    } else if !ablated("not") && matches!(&b2, Term::Op(XOR, p, q) if p.show() == a2.show() && matches!(**q, Term::Ones)) {
        // a + ~a = -1
        Some((Term::Ones, app2(memo(format!("not{n}"), || add_not_proof(n, false)).0, av, aw)))
    } else if !ablated("not") && !ablated("comm") && matches!(&a2, Term::Op(XOR, p, q) if p.show() == b2.show() && matches!(**q, Term::Ones)) {
        // ~b + b = b + ~b = -1
        let lemma = app2(memo(format!("not{n}"), || add_not_proof(n, false)).0, bv.clone(), bw.clone());
        let comm = apps(memo(format!("comm{n}"), || add_comm_proof(n, false)).0, vec![av, bv.clone(), aw, bw]);
        let swapped = witnessed(&Term::Op(ADD, Box::new(b2.clone()), Box::new(a2.clone())), n, goods).0;
        let ones = witnessed(&Term::Ones, n, goods).0;
        Some((Term::Ones, trans_proof(&bv_ty(n), &ev(&t1), &swapped, &ones, comm, lemma)))
    } else if let Some(r) = rule_step(n, &t1, goods) {
        Some(r)
    } else if let Some(r) = chain_step(n, &a2, &b2, goods) {
        Some(r)
    } else if let Some(r) = tree_step(n, &t1, goods) {
        Some(r)
    } else if let (false, Term::Op(ADD, p, q)) = (ablated("assoc"), &a2) {
        // (p + q) + r = p + (q + r)
        Some((sum(p, &sum(q, &b2)), assoc(p, q, &b2)))
    } else if let (false, Term::Op(ADD, bp, bq)) = (ablated("assoc") || ablated("comm"), &b2) {
        if bp.show() < a2.show() {
            // a + (b + c) = (a + b) + c = (b + a) + c = b + (a + c)
            let (a_, b_, c_) = (&a2, &**bp, &**bq);
            let ((av2, aw2), (bv2, bw2), (cv2, _)) = (witnessed(a_, n, goods), witnessed(b_, n, goods), witnessed(c_, n, goods));
            let (ab, ba) = (witnessed(&sum(a_, b_), n, goods).0, witnessed(&sum(b_, a_), n, goods).0);
            let comm = apps(memo(format!("comm{n}"), || add_comm_proof(n, false)).0, vec![av2, bv2, aw2, bw2]);
            let swap = cong_n(&bv_ty(n), &bv_ty(n), &ops[0], &[ab.clone(), cv2.clone()], &[ba.clone(), cv2.clone()], vec![comm, refl(cv2)]);
            let (acc, bc, a_bc) = (witnessed(&sum(&sum(a_, b_), c_), n, goods).0, witnessed(&sum(&sum(b_, a_), c_), n, goods).0, witnessed(&t1, n, goods).0);
            let target = sum(b_, &sum(a_, c_));
            let (to_ab_c, ab_c_to_ba_c, ba_c_to_target) = (sym(&bv_ty(n), &acc, &a_bc, assoc(a_, b_, c_)), swap, assoc(b_, a_, c_));
            let tv = witnessed(&target, n, goods).0;
            let first = trans_proof(&bv_ty(n), &witnessed(&t1, n, goods).0, &acc, &bc, to_ab_c, ab_c_to_ba_c);
            Some((target, trans_proof(&bv_ty(n), &witnessed(&t1, n, goods).0, &bc, &tv, first, ba_c_to_target)))
        } else {
            None
        }
    } else if !ablated("comm") && b2.show() < a2.show() {
        Some((sum(&b2, &a2), apps(memo(format!("comm{n}"), || add_comm_proof(n, false)).0, vec![av, bv, aw, bw])))
    } else {
        None
    };
    match step {
        None => (t1, cong),
        Some((t2, p)) => {
            let (t3, p3) = rewrite(&t2, n, ops, goods);
            let first = trans_proof(&bv_ty(n), &ev(t), &ev(&t1), &ev(&t2), cong, p);
            (t3.clone(), trans_proof(&bv_ty(n), &ev(t), &ev(&t2), &ev(&t3), first, p3))
        }
    }
}

/// `t` with each variable and each `add` subterm replaced by an atom variable (up to `cap`, by `show`).
pub fn abstract_atoms(t: &Term, atoms: &mut Vec<Term>, cap: usize) -> Option<Term> {
    match t {
        Term::Zero | Term::Ones => Some(t.clone()),
        Term::V(_) | Term::Op(ADD | SUB | SHL1 | SHR1, ..) => {
            let i = match atoms.iter().position(|a| a.show() == t.show()) {
                Some(i) => i,
                None => {
                    atoms.push(t.clone());
                    atoms.len() - 1
                }
            };
            (i < cap).then_some(Term::V(i))
        }
        Term::Op(o, a, b) => Some(Term::Op(*o, Box::new(abstract_atoms(a, atoms, cap)?), Box::new(abstract_atoms(b, atoms, cap)?))),
    }
}

// How many times `prove_eq` closed a pair with a whole-term machine proof (the rewriting did not finish the job).
// Per thread, so that the parallel miner's workers each read their own before/after difference.
thread_local! {
    pub static MACHINE_FALLBACKS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Pairs whose machines have more carries than this try generalizing a shared subterm first.
pub const GENERALIZE_ABOVE: usize = 3;

/// The subterm (with at least one `add` or `sub`, not a whole side) that occurs in both terms and has the most
/// carries, if any.
pub fn shared_subterm(a: &Term, b: &Term) -> Option<Term> {
    fn subs(t: &Term, out: &mut Vec<Term>) {
        if let Term::Op(_, x, y) = t {
            out.push(t.clone());
            subs(x, out);
            subs(y, out);
        }
    }
    let (mut sa, mut sb) = (vec![], vec![]);
    subs(a, &mut sa);
    subs(b, &mut sb);
    let in_b: std::collections::HashSet<String> = sb.iter().map(|t| t.show()).collect();
    sa.into_iter()
        .filter(|t| t.uses_add() && t.show() != a.show() && t.show() != b.show() && in_b.contains(&t.show()))
        .max_by_key(|t| Machine::parse(t).map_or(0, |m| m.carries()))
}

/// `t` with every occurrence of the subterm `x` replaced by `with`.
pub fn replace_term(t: &Term, x: &Term, with: &Term) -> Term {
    if t.show() == x.show() {
        return with.clone();
    }
    match t {
        Term::Op(o, a, b) => Term::Op(*o, Box::new(replace_term(a, x, with)), Box::new(replace_term(b, x, with))),
        _ => t.clone(),
    }
}

/// Proof of `Id(Bv_n, a, b)` in context `[x, y, gx, gy]` for rewritten terms: `refl`; the bitwise law over atoms
/// (when it holds on all four bit values, so the kernel check cannot fail); or, for two sums, `cong_n` on
/// proofs for their operands. `None` otherwise.
pub fn prove_eq(n: usize, ops: &[Expr], goods: &[(Expr, Expr)], a: &Term, b: &Term) -> Option<Expr> {
    let vals: Vec<Expr> = goods.iter().map(|g| g.0.clone()).collect();
    let ev = |t: &Term| t.eval(ops, n, &vals);
    if a.show() == b.show() {
        return Some(refl(ev(a)));
    }
    let (mut atoms, k) = (vec![], goods.len());
    if let (Some(a1), Some(a2)) = (abstract_atoms(a, &mut atoms, k), abstract_atoms(b, &mut atoms, k)) {
        let holds = (0..1usize << k).all(|m| {
            let bits: Vec<Expr> = (0..k).map(|v| bit(m >> v & 1 == 1)).collect();
            let truth = |t: &Term| normalize(&t.bit(&bits));
            truth(&a1) == truth(&a2)
        });
        if holds {
            let w: Vec<(Expr, Expr)> = (0..k).map(|i| atoms.get(i).map_or(goods[0].clone(), |t| witnessed(t, n, goods))).collect();
            let args = w.iter().map(|x| x.0.clone()).chain(w.iter().map(|x| x.1.clone())).collect();
            return Some(apps(bitwise_law_k(n, k, &a1, &a2).0, args));
        }
    }
    // add-free terms with shifts: the per-position prover, when the law holds exhaustively at widths 1..=5 (a position
    // reads only a few neighbours, so widths this small contain every case; the kernel checks the proof regardless)
    if k <= 3 && a.add_free() && b.add_free() && (a.has_shift() || b.has_shift()) {
        let holds = (1..=5usize).all(|w| (0..1u128 << (w * k)).all(|i| {
            let vals: Vec<u128> = (0..k).map(|v| (i >> (w * v)) & low_bits(w)).collect();
            a.interp(w, &vals) == b.interp(w, &vals)
        }));
        if holds {
            let args = goods.iter().map(|g| g.0.clone()).chain(goods.iter().map(|g| g.1.clone())).collect();
            return Some(apps(bitwise_law_k(n, k, a, b).0, args));
        }
    }
    if let (Term::Op(o @ (0 | 4), a1, a2), Term::Op(o2, b1, b2)) = (a, b)
        && o == o2
            && let (Some(p1), Some(p2)) = (prove_eq(n, ops, goods, a1, b1), prove_eq(n, ops, goods, a2, b2)) {
                return Some(cong_n(&bv_ty(n), &bv_ty(n), &ops[*o], &[ev(a1), ev(a2)], &[ev(b1), ev(b2)], vec![p1, p2]));
            }
    // equal bitwise operators: congruence on the operands
    if let (Term::Op(o, a1, a2), Term::Op(o2, b1, b2)) = (a, b)
        && o == o2 && *o != ADD && *o != SUB
            && let (Some(p1), Some(p2)) = (prove_eq(n, ops, goods, a1, b1), prove_eq(n, ops, goods, a2, b2)) {
                return Some(cong_n(&bv_ty(n), &bv_ty(n), &ops[*o], &[ev(a1), ev(a2)], &[ev(b1), ev(b2)], vec![p1, p2]));
            }
    if let Some(p) = shr_mask_eq(n, ops, goods, a, b) {
        return Some(p);
    }
    // a large pair: a subterm both sides share becomes one more variable (the witness of its value is built by
    // `witnessed`), which takes its carries out of the machine; the proof for the pair over `k + 1` variables
    // is the proof for the original pair, since the extra variable's value is the subterm's
    let cost = |t: &Term| Machine::parse(t).map_or(0, |m| m.carries());
    if cost(a).max(cost(b)) > GENERALIZE_ABOVE && k < VARS.len()
        && let Some(x) = shared_subterm(a, b) {
            let mut goods2 = goods.to_vec();
            goods2.push(witnessed(&x, n, goods));
            let (a2, b2) = (replace_term(a, &x, &Term::V(k)), replace_term(b, &x, &Term::V(k)));
            if let Some(p) = prove_eq(n, ops, &goods2, &a2, &b2) {
                return Some(p);
            }
        }
    // scoring mode: only whether the rewriting needed this fallback matters, so count it without building the machine proof
    if SCORE_ONLY.with(|s| s.get()) && Machine::parse(a).is_some() && Machine::parse(b).is_some() && cost(a).max(cost(b)) <= carry_cap() {
        MACHINE_FALLBACKS.with(|c| c.set(c.get() + 1));
        return Some(var(0));
    }
    // the carry-encoding proof for the two terms as bit-serial machines, at the variables' values
    let law = add_tree_law(n, k, a, b)?;
    MACHINE_FALLBACKS.with(|c| c.set(c.get() + 1));
    let args = goods.iter().map(|g| g.0.clone()).chain(goods.iter().map(|g| g.1.clone())).collect();
    Some(apps(law.0, args))
}

/// `shr1 A = shr1 B` (or `0 = shr1 B`, as `shr1 0`) for machine-expressible `A`, `B`, without a lookahead machine: the
/// bit-0 mask law `shr1 t = shr1 (t & M)`, `M = shl1 -1`, turns the pair into the shift-free law `A & M = B & M`
/// (search note section 47).
pub fn shr_mask_eq(n: usize, ops: &[Expr], goods: &[(Expr, Expr)], a: &Term, b: &Term) -> Option<Expr> {
    let (vals, bv) = (goods.iter().map(|g| g.0.clone()).collect::<Vec<_>>(), bv_ty(n));
    let ev = |t: &Term| t.eval(ops, n, &vals);
    let shr = |t: &Term| Term::Op(SHR1, Box::new(t.clone()), Box::new(Term::Zero));
    let (mask, one_arg) = (Term::Op(SHL1, Box::new(Term::Ones), Box::new(Term::Zero)), |t: &Term| match t {
        Term::Op(SHR1, x, _) if Machine::parse(x).is_some() => Some((**x).clone()),
        Term::Zero => Some(Term::Zero),
        _ => None,
    });
    if !matches!(a, Term::Op(SHR1, ..)) && !matches!(b, Term::Op(SHR1, ..)) {
        return None;
    }
    let (x, y) = (one_arg(a)?, one_arg(b)?);
    // the pair `A & M`, `B & M`: rewrite both, close with `prove_eq` (a machine law when they stay arithmetic)
    let (ta, tb) = (Term::Op(AND, Box::new(x.clone()), Box::new(mask.clone())), Term::Op(AND, Box::new(y.clone()), Box::new(mask.clone())));
    let ((r1, p1), (r2, p2)) = (rewrite(&ta, n, ops, goods), rewrite(&tb, n, ops, goods));
    let mid = prove_eq(n, ops, goods, &r1, &r2)?;
    let mid = trans_proof(&bv, &ev(&ta), &ev(&r1), &ev(&tb), p1, trans_proof(&bv, &ev(&r1), &ev(&r2), &ev(&tb), mid, sym(&bv, &ev(&tb), &ev(&r2), p2)));
    let cong = cong_n(&bv, &bv, &ops[7], &[ev(&ta), ev(&Term::Zero)], &[ev(&tb), ev(&Term::Zero)], vec![mid, refl(ev(&Term::Zero))]);
    // `a = shr1 (A & M)` and `b = shr1 (B & M)`
    let side_proof = |orig: &Term, arg: &Term| -> Option<Expr> {
        if matches!(orig, Term::Zero) {
            // `0 = shr1 0 = shr1 (0 & M)`: the second step is a congruence on `0 = 0 & M` by the rewriter
            let (r, pr) = rewrite(&Term::Op(AND, Box::new(Term::Zero), Box::new(mask.clone())), n, ops, goods);
            if r.show() != "0" {
                return None;
            }
            let (target, step) = rule_step(n, &shr(&Term::Zero), goods)?;
            if target.show() != "0" {
                return None;
            }
            let z = ev(&Term::Zero);
            let and0 = Term::Op(AND, Box::new(Term::Zero), Box::new(mask.clone()));
            let shr_and0 = shr(&and0);
            // shr1 0 = shr1 (0 & M) by congruence on `0 = 0 & M` (sym of the rewrite proof)
            let c = cong_n(&bv, &bv, &ops[7], &[z.clone(), z.clone()], &[ev(&and0), z.clone()], vec![sym(&bv, &ev(&and0), &z, pr), refl(z.clone())]);
            let zero_to_shr0 = sym(&bv, &ev(&shr(&Term::Zero)), &z, step);
            Some(trans_proof(&bv, &z, &ev(&shr(&Term::Zero)), &ev(&shr_and0), zero_to_shr0, c))
        } else {
            let law = memo(format!("shrmask{n}"), || {
                let (l, r) = (shr(&Term::V(0)), shr(&Term::Op(AND, Box::new(Term::V(0)), Box::new(Term::Op(SHL1, Box::new(Term::Ones), Box::new(Term::Zero))))));
                prove_rule(n, 1, &l, &r).expect("shrmask law")
            });
            let w = witnessed(arg, n, goods);
            Some(apps(law.0, vec![w.0, w.1]))
        }
    };
    let (pa, pb) = (side_proof(a, &x)?, side_proof(b, &y)?);
    let (sa, sb) = (shr(&ta), shr(&tb));
    let first = trans_proof(&bv, &ev(a), &ev(&sa), &ev(&sb), pa, cong);
    Some(trans_proof(&bv, &ev(a), &ev(&sb), &ev(b), first, sym(&bv, &ev(b), &ev(&sb), pb)))
}

/// Proof of `t1 = t2` over two good vectors by rewriting both sides and closing with `prove_eq`; `None` when
/// that cannot.
pub fn rewrite_law(n: usize, k: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    let ops = ops_for(n);
    let goods: Vec<(Expr, Expr)> = (0..k).map(|i| (var((2 * k - 1 - i) as u32), var((k - 1 - i) as u32))).collect();
    let vals: Vec<Expr> = goods.iter().map(|g| g.0.clone()).collect();
    let ev = |t: &Term| t.eval(&ops, n, &vals);
    let bv = bv_ty(n);
    // an `lt` root (a one-bit result) is rewritten under its operands, then closed by congruence or, failing that,
    // by the `lt` machine proof for the rewritten pair; `lt` occurs only at the root
    let lt_roots = matches!((t1, t2), (Term::Op(LT, ..), Term::Op(LT, ..)));
    let root = if lt_roots { bv_ty(1) } else { bv.clone() };
    let (r1, p1, r2, p2, mid) = if lt_roots {
        // `rewrite` normalizes the operands and applies the root rules; equal results close by `refl`, `lt` roots with
        // provable operands by congruence, the rest by the `lt` machine proof of the rewritten pair
        let ((r1, p1), (r2, p2)) = (rewrite(t1, n, &ops, &goods), rewrite(t2, n, &ops, &goods));
        let mid = if r1.show() == r2.show() {
            refl(ev(&r1))
        } else {
            let by_operands = if let (Term::Op(LT, a2, b2), Term::Op(LT, c2, d2)) = (&r1, &r2) {
                match (prove_eq(n, &ops, &goods, a2, c2), prove_eq(n, &ops, &goods, b2, d2)) {
                    (Some(pa), Some(pb)) => Some(cong_n(&bv, &root, &ops[5], &[ev(a2), ev(b2)], &[ev(c2), ev(d2)], vec![pa, pb])),
                    _ => None,
                }
            } else {
                None
            };
            match by_operands {
                Some(proof) => proof,
                None => {
                    let law = add_tree_law(n, k, &r1, &r2)?;
                    MACHINE_FALLBACKS.with(|c| c.set(c.get() + 1));
                    apps(law.0, goods.iter().map(|g| g.0.clone()).chain(goods.iter().map(|g| g.1.clone())).collect())
                }
            }
        };
        (r1, p1, r2, p2, mid)
    } else {
        let (r1, p1) = rewrite(t1, n, &ops, &goods);
        let (r2, p2) = rewrite(t2, n, &ops, &goods);
        match prove_eq(n, &ops, &goods, &r1, &r2) {
            Some(mid) => (r1, p1, r2, p2, mid),
            // the rewriter may have pushed the shifts down to atoms; the mask reduction applies to the original sides
            None => (t1.clone(), refl(ev(t1)), t2.clone(), refl(ev(t2)), shr_mask_eq(n, &ops, &goods, t1, t2)?),
        }
    };
    let to_r2 = trans_proof(&root, &ev(t1), &ev(&r1), &ev(&r2), p1, mid);
    let body = trans_proof(&root, &ev(t1), &ev(&r2), &ev(t2), to_r2, sym(&root, &ev(t2), &ev(&r2), p2));
    let (mut proof, mut stmt) = (body, id(root.clone(), ev(t1), ev(t2)));
    for _ in 0..k {
        let g = app(good_bv(n), var(k as u32 - 1));
        (proof, stmt) = (lam(g.clone(), proof), pi(g, stmt));
    }
    for _ in 0..k {
        (proof, stmt) = (lam(bv.clone(), proof), pi(bv.clone(), stmt));
    }
    Some((proof, stmt))
}

#[test]
pub fn laws_over_three_vectors_check_and_false_ones_fail() {
    let _scope = tatic::kernel::InternScope::enter();
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    for n in [1usize, 3] {
        // bitwise (x ^ y) ^ z = x ^ (y ^ z)
        let (p, s) = bitwise_law_k(n, 3, &op(3, op(3, v(0), v(1)), v(2)), &op(3, v(0), op(3, v(1), v(2))));
        ck(&format!("xor assoc at n={n}"), &p, &s);
        assert!(check(&Ctx::new(), &bitwise_law_k(n, 3, &op(1, v(0), v(2)), &op(2, v(0), v(2))).0, &bitwise_law_k(n, 3, &op(1, v(0), v(2)), &op(2, v(0), v(2))).1).is_err());
        // add associativity over three vectors, and a non-law
        let (p, s) = rewrite_law(n, 3, &op(0, op(0, v(0), v(1)), v(2)), &op(0, v(0), op(0, v(1), v(2)))).expect("assoc");
        ck(&format!("add assoc at n={n}"), &p, &s);
        let (p, s) = rewrite_law(n, 3, &op(0, op(0, v(2), v(0)), v(1)), &op(0, v(1), op(0, v(0), v(2)))).expect("comm+assoc");
        ck(&format!("add comm assoc at n={n}"), &p, &s);
        assert!(rewrite_law(n, 3, &op(0, v(0), v(2)), &op(0, v(0), v(1))).is_none());
    }
}

#[test]
pub fn rewrite_law_proves_add_conjectures_from_the_library_lemmas() {
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    let n = 4;
    for (name, t1, t2) in [
        ("or (add x 0) y = or y x", op(2, op(0, v(0), Term::Zero), v(1)), op(2, v(1), v(0))),
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

// ---- Carry-chain builder (search note section 13): `add A B = T` for bitwise A, B, T over x, y, with no
// lemma-specific template. It *discovers* the proof invariant: a constant value R for the carry that is
// inductive (the carry stays R for every pair of operand bits, starting from the initial `false`) and under
// which every sum bit equals the target bit. Both are decided by truth table before anything is built.

/// The constant carry value (as a literal bit) that works for `add a b = t`, if any.
pub fn find_constant_carry(a: &Term, b: &Term, t: &Term) -> Option<bool> {
    let carry = |x: Expr, y: Expr, c: Expr| or(and(x.clone(), y.clone()), and(c, xor(x, y)));
    [false, true].into_iter().find(|&r| {
        // the initial carry is `false`, so only `false` can be maintained from the start
        !r && (0..4).all(|m| {
            let bits = [bit(m & 1 == 1), bit(m & 2 == 2)];
            let (ab, bb, tb) = (a.bit(&bits), b.bit(&bits), t.bit(&bits));
            normalize(&carry(ab.clone(), bb.clone(), bit(r))) == bit(r) && normalize(&sum3(ab, bb, bit(r))) == normalize(&tb)
        })
    })
}

/// Proof of `t1 = t2` where `t1 = add A B` (bitwise `A`, `B`) and `t2` is bitwise, over two good vectors, by the
/// discovered constant-carry invariant; `None` when no constant carry works.
pub fn carry_chain_law(n: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    let Term::Op(ADD, a_term, b_term) = t1 else { return None };
    if a_term.uses_add() || b_term.uses_add() || t2.uses_add() || t1.max_var().max(t2.max_var()) > 1 {
        return None;
    }
    let r = bit(find_constant_carry(a_term, b_term, t2)?);
    let carry = |x: Expr, y: Expr, c: Expr| or(and(x.clone(), y.clone()), and(c, xor(x, y)));
    // per-bit lemmas, by case analysis on the two operand bits
    let (p_carry, _) = lemma2(
        &|x, y| id(bool0(), carry(a_term.bit(&[x.clone(), y.clone()]), b_term.bit(&[x.clone(), y.clone()]), r.clone()), r.clone()),
        &|_, _| refl(r.clone()),
    );
    let (p_sum, _) = lemma2(
        &|x, y| id(bool0(), sum3(a_term.bit(&[x.clone(), y.clone()]), b_term.bit(&[x.clone(), y.clone()]), r.clone()), t2.bit(&[x, y])),
        &|vx, vy| refl(t2.bit(&[bit(vx), bit(vy)])),
    );
    Some(two_var_law(n, t1, t2, &|a, ga, b, gb| {
        let bl = bool0();
        let (ai, bi) = (|i: usize| a_term.bit(&[a(i), b(i)]), |i: usize| b_term.bit(&[a(i), b(i)]));
        let mut c = vec![r.clone()];
        let mut pc: Vec<Option<Expr>> = vec![None];
        let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
        for i in 0..n {
            let args = vec![a(i), b(i), ga(i), gb(i)];
            // sum bit: rewrite the carry to R, then the sum lemma
            let s_i = sum3(ai(i), bi(i), c[i].clone());
            let to_target = apps(p_sum.clone(), args.clone());
            e.push(match &pc[i] {
                None => to_target,
                Some(pci) => {
                    let fmap = lam(bl.clone(), sum3(shift(&ai(i), 0, 1), shift(&bi(i), 0, 1), var(0)));
                    let rewritten = cong1(&bl, &bl, &fmap, c[i].clone(), r.clone(), pci.clone());
                    trans_proof(&bl, &s_i, &sum3(ai(i), bi(i), r.clone()), &t2.bit(&[a(i), b(i)]), rewritten, to_target)
                }
            });
            s1.push(s_i);
            s2.push(t2.bit(&[a(i), b(i)]));
            // next carry stays R
            let next = carry(ai(i), bi(i), c[i].clone());
            let stays = apps(p_carry.clone(), args);
            pc.push(Some(match &pc[i] {
                None => stays,
                Some(pci) => {
                    let fmap = lam(bl.clone(), carry(shift(&ai(i), 0, 1), shift(&bi(i), 0, 1), var(0)));
                    let rewritten = cong1(&bl, &bl, &fmap, c[i].clone(), r.clone(), pci.clone());
                    trans_proof(&bl, &next, &carry(ai(i), bi(i), r.clone()), &r, rewritten, stays)
                }
            }));
            c.push(next);
        }
        (s1, s2, e)
    }))
}

#[test]
pub fn carry_chain_builder_finds_the_constant_carry() {
    let v = |i: usize| Term::V(i);
    let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
    for n in [1usize, 2, 4] {
        for (name, t1, t2) in [
            ("add x (xor x -1) = -1", op(0, v(0), op(3, v(0), Term::Ones)), Term::Ones),
            ("add (xor -1 y) y = -1", op(0, op(3, Term::Ones, v(1)), v(1)), Term::Ones),
            ("add x 0 = x", op(0, v(0), Term::Zero), v(0)),
            ("add (and x 0) y = y", op(0, op(1, v(0), Term::Zero), v(1)), v(1)),
        ] {
            let (p, s) = carry_chain_law(n, &t1, &t2).unwrap_or_else(|| panic!("{name}: no constant carry"));
            ck(&format!("{name} at n={n}"), &p, &s);
        }
        // no constant carry exists for these
        assert!(carry_chain_law(n, &op(0, v(0), v(1)), &op(0, v(1), v(0))).is_none());
        assert!(carry_chain_law(n, &op(0, v(0), Term::Ones), &v(0)).is_none());
    }
}

// ---- Searching for the carry-state encoding (search note sections 14 and 15). A sum tree of `c + 1` leaves (each
// leaf an add-free bitwise term over `k` vectors) is a ripple machine with `c` carries, one per `add` node. Two
// such sums agree if some encoding phi = (phi_1..phi_m) of the carry vector (m Boolean functions of the `c`
// carries) carries enough information: each side's output bit and next phi-values must be functions of (the `k`
// operand bits, phi(carries)), the same functions on both sides. `moore_encoding` computes the coarsest one by partition
// refinement; the proof is the associativity proof with the discovered phi in
// place of the hand-derived (xor, and) -- for a three-leaf sum, the total carry in binary.

/// `lpo_greater` is a strict total order on the terms over two variables up to 4 nodes, and closed under contexts.
#[test]
fn lpo_is_a_strict_total_order_closed_under_contexts() {
    let b = |o: usize, a: &Term, c: &Term| Term::Op(o, Box::new(a.clone()), Box::new(c.clone()));
    let mut by_size: Vec<Vec<Term>> = vec![vec![], vec![Term::V(0), Term::V(1), Term::Zero, Term::Ones]];
    for sz in 2..=4 {
        let mut level = vec![];
        for i in 1..sz - 1 {
            for l in &by_size[i] {
                for r in &by_size[sz - 1 - i] {
                    for o in 0..8 {
                        level.push(b(o, l, r));
                    }
                }
            }
        }
        by_size.push(level);
    }
    let all: Vec<Term> = by_size.into_iter().flatten().collect();
    for s in &all {
        assert!(!lpo_greater(s, s));
        for t in &all {
            if s.show() != t.show() {
                assert!(lpo_greater(s, t) ^ lpo_greater(t, s), "{} vs {}", s.show(), t.show());
                if lpo_greater(s, t) {
                    for o in [0usize, 4] {
                        assert!(lpo_greater(&b(o, s, &Term::V(0)), &b(o, t, &Term::V(0))));
                        assert!(lpo_greater(&b(o, &Term::V(1), s), &b(o, &Term::V(1), t)));
                    }
                }
            }
        }
    }
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
