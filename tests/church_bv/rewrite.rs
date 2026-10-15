use super::*;

/// Compared and hashed structurally; `show()` is for text (files, logs, lemma names) and the text orders, never for equality.
/// The derived `Ord` only makes canonical keys (a sorted rule set); the rewriter's orders are on `show()`.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
        let mut s = String::new();
        self.show_into(&mut s);
        s
    }
    fn show_into(&self, out: &mut String) {
        match self {
            Term::V(i) => out.push_str(VARS[*i]),
            Term::Zero => out.push('0'),
            Term::Ones => out.push_str("-1"),
            Term::Op(o, a, b) => {
                out.push_str(OP_INFO[*o].name);
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
        self.counterexample_in(other, n, k, 204)
    }
    /// `counterexample` over the first `tries` tuples only.
    pub fn counterexample_in(&self, other: &Term, n: usize, k: usize, tries: usize) -> Option<Vec<u128>> {
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
            assert!(holds(&p, &s).is_err(), "false law `{name}` must be rejected at n={n}");
        }
    }
}

// ---- Rewriting with proven lemmas (search note section 10). An `add` conjecture is simplified on both sides by
// the library lemmas `add a 0 = a`, `add 0 a = a` and `add a b = add b a` (the last used to order the operands),
// each rewrite justified by `cong_n` on the enclosing operator and chained with `trans_proof`; if the two
// results are then equal, or both add-free, `bitwise_law` closes the gap.

thread_local! {
    pub static CLOSED: std::cell::RefCell<std::collections::HashMap<String, (tatic::kernel::PExpr, tatic::kernel::PExpr)>> = Default::default();
}
/// A closed library term built once per key (the proofs and witnesses the rewriter reuses at every step).
pub fn memo(key: String, build: impl FnOnce() -> (Expr, Expr)) -> (Expr, Expr) {
    if let Some(v) = CLOSED.with(|c| c.borrow().get(&key).map(|(p, s)| (p.get(), s.get()))) {
        return v;
    }
    let (p, s) = build();
    CLOSED.with(|c| c.borrow_mut().insert(key, (tatic::kernel::persist(p.clone()), tatic::kernel::persist(s.clone()))));
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
            let r = ps.bind(s.clone());
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
    match t {
        Term::V(i) => goods[*i].clone(),
        Term::Zero => (lit(n, 0), good_lit(n, 0)),
        Term::Ones => (lit(n, all), good_lit(n, all)),
        Term::Op(o, a, b) => {
            let ((av, aw), (bv, bw)) = (witnessed(a, n, goods), witnessed(b, n, goods));
            let (op, good_op) = match o {
                0 => (add(n), shared_lemma(format!("good_add{n}"), || good_add(n)).0),
                4 => (sub(n), shared_lemma(format!("good_sub{n}"), || good_sub(n)).0),
                6 => (shl1_op(n), shared_lemma(format!("good_shl1{n}"), || good_shl1(n)).0),
                7 => (shr1_op(n), shared_lemma(format!("good_shr1{n}"), || good_shr1(n)).0),
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
        PlanRc::new(Plan::Refl(t.clone()))
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
    (0..k).map(Term::V).collect()
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
        Compiler { n, ops: ops_for(n), vals: goods.iter().map(|g| g.0.clone()).collect(), goods }
    }

    pub fn ev(&self, t: &Term) -> Expr {
        t.eval(&self.ops, self.n, &self.vals)
    }

    /// The type of `t`'s value: one bit under an `lt` root, else `n` bits.
    fn ty(&self, t: &Term) -> Expr {
        bv_ty(if matches!(t, Term::Op(LT, ..)) { 1 } else { self.n })
    }

    /// The plan's two sides and the proof of `Id(lhs, rhs)`.
    pub fn proof(&self, plan: &Plan) -> (Term, Term, Expr) {
        let n = self.n;
        match plan {
            Plan::Refl(t) => (t.clone(), t.clone(), refl(self.ev(t))),
            Plan::Cong(o, a, b) => {
                let ((a1, a2, pa), (b1, b2, pb)) = (self.proof(a), self.proof(b));
                let (xs, ys) = ([self.ev(&a1), self.ev(&b1)], [self.ev(&a2), self.ev(&b2)]);
                let (l, r) = (Term::Op(*o, Box::new(a1), Box::new(b1)), Term::Op(*o, Box::new(a2), Box::new(b2)));
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
                let p = apps(law, w.iter().map(|x| x.0.clone()).chain(w.iter().map(|x| x.1.clone())).collect());
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
    let cand = [Term::Zero, Term::Ones, Term::V(0), Term::V(1)]
        .into_iter()
        .find(|cand| !matches!(cand, Term::V(i) if *i >= atoms.len()) && find_constant_carry(&a1, &b1, cand).is_some())?;
    let target = if let Term::V(i) = cand { atoms[i].clone() } else { cand.clone() };
    let args = (0..2).map(|i| atoms.get(i).cloned().unwrap_or(Term::V(0))).collect();
    Some((target, Plan::law(LawKind::Chain, Term::Op(ADD, Box::new(a1), Box::new(b1)), cand, args)))
}

/// A sum tree of add-free leaves that the carry-encoding search shows equal to a constant, a variable or one
/// bitwise operation on two of them (so `-1 - x` becomes `x ^ -1`): that value and
/// the plan (`add_tree_law` over the `k` variables). Ablation name `tree`.
pub fn tree_step(n: usize, t1: &Term, k: usize) -> Option<(Term, PlanRc)> {
    if ablated("tree") {
        return None;
    }
    // the constants, the variables, then every operator applied to two of them (a plain-integer screen in
    // `tree_encoding` discards the false candidates cheaply)
    let cand = [Term::Zero, Term::Ones]
        .into_iter()
        .chain((0..k).map(Term::V))
        .chain(terms(k, false).into_iter().filter(|c| matches!(c, Term::Op(o, ..) if (1..=3).contains(o))))
        .find(|cand| tree_encoding(n, k, t1, cand).is_some())?;
    Some((cand.clone(), Plan::law(LawKind::Tree, t1.clone(), cand, vars(k))))
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
    /// Rules added at run time (by the rule miner), after the built-in ones, in `set_extra_rules` order. Write it only through
    /// `set_extra_rules` (or clear it).
    pub static EXTRA_RULES: std::cell::RefCell<Vec<(Term, Term)>> = Default::default();
    /// While `Some`, `rule_step` records every term it is asked to rewrite: a rule added anywhere in the rule list can change a
    /// rewriting only if its left side matches one of them.
    pub static RULE_TRACE: std::cell::RefCell<Option<Vec<Term>>> = const { std::cell::RefCell::new(None) };
    /// Learned rule preferences, (winner, loser): where both rules would rewrite a term, the winner does, whatever the order
    /// (docs/tier-cycle.md, "Rule order"). Set with the rules they belong to (`set_rule_prefs`).
    pub static RULE_PREFS: std::cell::RefCell<std::collections::HashSet<Pref>> = Default::default();
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
            p.remove(&(l.clone(), w.clone()));
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
    let reverse = (prefs[0].1.clone(), prefs[0].0.clone());
    assert_eq!(step(vec![prefs[0].clone(), reverse]), plain);
}

/// Installs `rules` as the run-time rules, most specific first: larger left sides first, ties by text. `rule_step` applies the first
/// rule that matches, so a library's order would otherwise change its normal forms: the same pooled library served in six orders
/// gave total M 47-62 on add3 (docs/tier-cycle.md, "Rule order"). Any order of the same rules now serves identically.
pub fn set_extra_rules(mut rules: Vec<(Term, Term)>) {
    rules.sort_by_cached_key(|(l, r)| (std::cmp::Reverse(l.size()), l.show(), r.show()));
    EXTRA_RULES.with(|e| *e.borrow_mut() = rules);
}

#[test]
fn rule_order_does_not_change_rewriting() {
    // overlapping rules: under list order the first one would win on sub(sub(x, y), z) whichever it is
    let a = "sub(sub(x, y), z) -> sub(x, add(y, z))\nsub(x, y) -> add(x, sub(0, y))\nsub(sub(x, y), z) -> sub(sub(x, z), y)\n";
    let b = "sub(sub(x, y), z) -> sub(sub(x, z), y)\nsub(x, y) -> add(x, sub(0, y))\nsub(sub(x, y), z) -> sub(x, add(y, z))\n";
    let installed = |text: &str| {
        set_extra_rules(parse_rules(text));
        let shown: Vec<String> = EXTRA_RULES.with(|e| e.borrow().iter().map(|(l, r)| format!("{} -> {}", l.show(), r.show())).collect());
        EXTRA_RULES.with(|e| e.borrow_mut().clear());
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
        parse_rules(&text)
    })
}

/// The rules that do not change during a run, in the order `rule_step` tries them: the built-ins, the promoted rules, the
/// `RULESET` rules; the mined ones (`EXTRA_RULES`) come after them. Built once per process.
pub fn fixed_rules() -> &'static [Rule] {
    static RULES: std::sync::OnceLock<Vec<Rule>> = std::sync::OnceLock::new();
    RULES.get_or_init(build_fixed_rules)
}

fn build_fixed_rules() -> Vec<Rule> {
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
    let mut seen = std::collections::HashSet::new();
    text.lines().filter(|l| !l.contains("  OVER  ")).filter_map(|l| l.split_once(" -> ")).map(|(a, b)| (parse_term(a), parse_term(b))).filter(|r| seen.insert(r.clone())).collect()
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
        match t {
            Term::V(i) => Term::V(i + k),
            Term::Op(o, a, b) => Term::Op(*o, Box::new(shift(a, k)), Box::new(shift(b, k))),
            _ => t.clone(),
        }
    }
    // `t` with one non-variable position unified with `l` and replaced by `r`, and the unifier
    fn at(t: &Term, l: &Term, r: &Term, nv: usize) -> Vec<(Vec<Option<Term>>, Term)> {
        let mut out = vec![];
        if let Term::Op(o, a, b) = t {
            let mut s = vec![None; nv];
            if unify(t, l, &mut s) {
                out.push((s, r.clone()));
            }
            out.extend(at(a, l, r, nv).into_iter().map(|(s, a2)| (s, Term::Op(*o, Box::new(a2), b.clone()))));
            out.extend(at(b, l, r, nv).into_iter().map(|(s, b2)| (s, Term::Op(*o, a.clone(), Box::new(b2)))));
        }
        out
    }
    fn apply(t: &Term, s: &[Option<Term>]) -> Term {
        match t {
            Term::V(i) => s[*i].as_ref().map_or_else(|| t.clone(), |b| apply(b, s)),
            Term::Op(o, a, b) => Term::Op(*o, Box::new(apply(a, s)), Box::new(apply(b, s))),
            _ => t.clone(),
        }
    }
    fn renumber(t: &Term, seen: &mut Vec<usize>) -> Term {
        match t {
            Term::V(i) => Term::V(seen.iter().position(|j| j == i).unwrap_or_else(|| {
                seen.push(*i);
                seen.len() - 1
            })),
            Term::Op(o, a, b) => Term::Op(*o, Box::new(renumber(a, seen)), Box::new(renumber(b, seen))),
            _ => t.clone(),
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
    EXTRA_RULES.with(|e| e.borrow_mut().clear());
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
    let own = (l.clone(), r.clone());
    let notsub = fixed_rules().iter().find(|x| x.name == "notsub").map(|x| (x.lhs.clone(), x.rhs.clone()))?;
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
    let stmt = pi(g.clone(), id(bv.clone(), ev(&l), ev(&r)));
    Some((lam(bv.clone(), lam(g, body)), pi(bv, stmt)))
}

/// The law behind a rule: bitwise/shift rules by the per-position prover, the rest by the carry machines.
pub fn prove_rule(n: usize, k: usize, l: &Term, r: &Term) -> Option<(Expr, Expr)> {
    if (l, r) == (&shrnot_rule().0, &shrnot_rule().1) {
        shr_not_law(n)
    } else if l.add_free() && r.add_free() {
        let law = bitwise_law_k(n, k, l, r);
        holds(&law.0, &law.1).ok().map(|_| law)
    } else if matches!(l, Term::Op(SHR1, ..)) && matches!(r, Term::Op(SHR1, ..) | Term::Zero) || matches!(r, Term::Op(SHR1, ..)) && matches!(l, Term::Zero) {
        // laws with a `shr1` root are not machines: prove them with the rewriter (which falls back on the bit-0 mask
        // reduction), without the rule being proved, so that it cannot be used in its own proof
        proving(&[(l.clone(), r.clone())], || rewrite_law(n, k, l, r))
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
                if a != b {
                    return a.size() > b.size() || (a.size() == b.size() && tie_greater(a, b));
                }
            }
            false
        }
        (Term::Op(..), _) => true,
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

pub fn match_pat(p: &Term, t: &Term, sub: &mut Vec<Option<Term>>) -> bool {
    match (p, t) {
        (Term::V(i), _) => match &sub[*i] {
            Some(b) => b == t,
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

/// Syntactic unification of `a` and `b` (variables shared, bindings in `sub`), with the occurs check.
pub fn unify(a: &Term, b: &Term, sub: &mut Vec<Option<Term>>) -> bool {
    fn resolve(t: &Term, sub: &[Option<Term>]) -> Term {
        match t {
            Term::V(i) => sub[*i].as_ref().map_or_else(|| t.clone(), |b| resolve(b, sub)),
            _ => t.clone(),
        }
    }
    fn occurs(i: usize, t: &Term, sub: &[Option<Term>]) -> bool {
        match resolve(t, sub) {
            Term::V(j) => i == j,
            Term::Op(_, x, y) => occurs(i, &x, sub) || occurs(i, &y, sub),
            _ => false,
        }
    }
    match (resolve(a, sub), resolve(b, sub)) {
        (Term::V(i), Term::V(j)) if i == j => true,
        (Term::V(i), t) | (t, Term::V(i)) => {
            if occurs(i, &t, sub) {
                return false;
            }
            sub[i] = Some(t);
            true
        }
        (Term::Zero, Term::Zero) | (Term::Ones, Term::Ones) => true,
        (Term::Op(o, x1, y1), Term::Op(o2, x2, y2)) => o == o2 && unify(&x1, &x2, sub) && unify(&y1, &y2, sub),
        _ => false,
    }
}

/// The overlaps among `rules`: (i, j, at root) for each rule j whose left side unifies with a non-variable subterm of rule i's left
/// side (variables renamed apart; a rule with itself only below the root). Where two left sides overlap, first-match order decides
/// which rule rewrites, so these are the pairs a rule order (or completion) has to settle.
pub fn rule_overlaps(rules: &[(Term, Term)]) -> Vec<(usize, usize, bool)> {
    fn shift(t: &Term, k: usize) -> Term {
        match t {
            Term::V(i) => Term::V(i + k),
            Term::Op(o, a, b) => Term::Op(*o, Box::new(shift(a, k)), Box::new(shift(b, k))),
            _ => t.clone(),
        }
    }
    fn subterms<'a>(t: &'a Term, root: bool, out: &mut Vec<(&'a Term, bool)>) {
        if let Term::Op(_, a, b) = t {
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
    let touched: std::collections::HashSet<usize> = o.iter().flat_map(|&(i, j, _)| [i, j]).collect();
    println!(
        "OVERLAPS {} rules, {} overlapping pairs: {} inner, {} at the root with one left side an instance of the other, {} at the root otherwise; {} rules in some overlap",
        rules.len(), o.len(), kinds[0], kinds[1], kinds[2], touched.len()
    );
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

/// A rule as `rule_step` tries it, borrowed from `fixed_rules` or from `EXTRA_RULES` (rebuilding and cloning the rule list
/// on every step was 10% of a mine).
#[derive(Clone, Copy)]
struct RuleRef<'a> {
    name: &'static str,
    lhs: &'a Term,
    rhs: &'a Term,
}

impl RuleRef<'_> {
    fn is(&self, (l, r): &RuleKey) -> bool {
        self.lhs == l && self.rhs == r
    }
    fn key(&self) -> RuleKey {
        (self.lhs.clone(), self.rhs.clone())
    }
}

/// `RULE_CONFLICTS=1` (experiment): for each (rule that rewrote a term, later rule that would also have), how many terms; `print_rule_conflicts` lists them.
pub static RULE_CONFLICTS: std::sync::Mutex<Option<std::collections::HashMap<Pref, u64>>> = std::sync::Mutex::new(None);

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
    RULE_TRACE.with(|tr| {
        if let Some(v) = tr.borrow_mut().as_mut() {
            v.push(t.clone());
        }
    });
    EXTRA_RULES.with(|mined| rule_step_in(t, &mined.borrow()))
}

fn rule_step_in(t: &Term, mined: &[(Term, Term)]) -> Option<(Term, PlanRc)> {
    let fixed = fixed_rules().iter().map(|r| RuleRef { name: r.name, lhs: &r.lhs, rhs: &r.rhs });
    let all: Vec<RuleRef> = fixed.chain(mined.iter().map(|(l, r)| RuleRef { name: "mined", lhs: l, rhs: r })).collect();
    let fires = |r: &RuleRef| -> Option<Vec<Option<Term>>> {
        let mut sub = vec![None; r.lhs.max_var().max(r.rhs.max_var()) + 1];
        if ablated(r.name) || !match_pat(r.lhs, t, &mut sub) {
            return None;
        }
        if PROVING.with(|p| p.borrow().iter().any(|k| r.is(k))) {
            return None;
        }
        // a rule whose right side is an instance of its own left side (`lt(x,x) -> lt(-1,-1)`) must not rewrite its result
        let inst = subst_pat(r.rhs, &sub.iter().map(|s| s.clone().or(Some(Term::Zero))).collect::<Vec<_>>());
        if inst == *t {
            return None;
        }
        // a permutative rule (ordered rewriting): only when the instance goes down in the order on `show()` strings
        // (a path order on every tied instance, `PERM_ORDER=lpo`, raised M, and the tie-break order before `show()`, `PERM_ORDER=tie`,
        // never became the default; the rewrite cycles both targeted are cut in `rewrite` instead: docs/tier-cycle.md)
        if rule_permutative(r.lhs, r.rhs) && inst.show_cmp(t).is_ge() {
            return None;
        }
        Some(sub)
    };
    let (mut i, mut sub) = all.iter().enumerate().find_map(|(i, r)| fires(r).map(|s| (i, s)))?;
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
            match all.iter().enumerate().find_map(|(j, r)| if j != i && winners.iter().any(|w| r.is(w)) { fires(r).map(|s| (j, s)) } else { None }) {
                Some(next) => (i, sub) = next,
                None => break,
            }
        }
    });
    if let Some(m) = RULE_CONFLICTS.lock().unwrap().as_mut() {
        for r in all.iter().skip(i + 1).filter(|r| fires(r).is_some()) {
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
    let args = sub.iter().map(|s| s.clone().unwrap_or(Term::V(0))).collect();
    let mut hits = RULE_HITS.lock().unwrap();
    match hits.iter_mut().find(|h| h.0 == r.name) {
        Some(h) => h.1 += 1,
        None => hits.push((r.name, 1)),
    }
    Some((subst_pat(r.rhs, &sub), Plan::law(LawKind::Rule(r.name), r.lhs.clone(), r.rhs.clone(), args)))
}

/// A cached `rewrite`: the result and what the call did besides returning it, so that a hit can replay it.
struct Rewritten {
    out: (Term, PlanRc),
    /// rule steps used (`RULE_BUDGET`): a hit needs at least this many left
    steps: i64,
    fallbacks: u64,
    /// the terms `rule_step` was asked about (`RULE_TRACE`), when `traced` (the trace was on)
    trace: Vec<Term>,
    traced: bool,
}

/// While `Some`, `rewrite` calls over `k` variables are cached by (width, term). The rule miner sets it for one rule set
/// (one `score_laws` call): the result of `rewrite` is a function of the term, the rules in force and the budget left, so a repeat
/// under the same rules is a hit. Calls over other variable counts (the generalization path adds witnesses) are not cached.
pub struct RewriteMemo {
    k: usize,
    map: std::collections::HashMap<(usize, Term), std::rc::Rc<Rewritten>>,
}

impl RewriteMemo {
    pub fn new(k: usize) -> RewriteMemo {
        RewriteMemo { k, map: Default::default() }
    }

    /// The traced entries whose traces `keep` accepts. A rule tried after the others changes no entry whose trace it matches
    /// nowhere, so the rule miner seeds each candidate's scoring with the entries of the rules chosen so far that the candidate
    /// cannot change.
    pub fn filtered(&self, keep: impl Fn(&[Term]) -> bool) -> RewriteMemo {
        RewriteMemo { k: self.k, map: self.map.iter().filter(|(_, e)| e.traced && keep(&e.trace)).map(|(k, e)| (k.clone(), e.clone())).collect() }
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
}

/// `s` homeomorphically embeds in `t`: `t` is `s` with nodes inserted (Kruskal). Between terms of equal size it is equality.
fn embeds(s: &Term, t: &Term) -> bool {
    let couple = match (s, t) {
        (Term::V(i), Term::V(j)) => i == j,
        (Term::Zero, Term::Zero) | (Term::Ones, Term::Ones) => true,
        (Term::Op(f, s1, s2), Term::Op(g, t1, t2)) => f == g && embeds(s1, t1) && embeds(s2, t2),
        _ => false,
    };
    couple || matches!(t, Term::Op(_, t1, t2) if embeds(s, t1) || embeds(s, t2))
}

/// `t` (over `k` variables) rewritten bottom-up, with the plan of `t = t'` (`Compiler` proves it). Rewriting is deterministic apart from
/// the step budget, so a call `rewrite(t)` made while `t` itself is being rewritten further out can only repeat that work until the
/// budget runs out: a rewrite cycle. A chain that returns to a larger copy of a term it is rewriting (one that term embeds in) is
/// taken to grow without end. The cut returns `t` unchanged in both cases, so the chain ends one lap round instead of at the budget
/// (docs/tier-cycle.md, "Cycle cut").
pub fn rewrite(t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    if !matches!(t, Term::Op(..)) {
        return rewrite_memo(t, n, k);
    }
    let size = t.size();
    if REWRITE_PATH.with(|p| p.borrow().iter().any(|s| s.size() <= size && embeds(s, t))) {
        CYCLE_CUTS.with(|c| c.set(c.get() + 1));
        return (t.clone(), Plan::refl(t));
    }
    REWRITE_PATH.with(|p| p.borrow_mut().push(t.clone()));
    let out = rewrite_memo(t, n, k);
    REWRITE_PATH.with(|p| p.borrow_mut().pop());
    out
}

fn rewrite_memo(t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    let on = matches!(t, Term::Op(..)) && REWRITE_MEMO.with(|m| m.borrow().as_ref().is_some_and(|m| m.k == k));
    if !on {
        return rewrite_uncached(t, n, k);
    }
    let key = (n, t.clone());
    let hit = REWRITE_MEMO.with(|m| m.borrow().as_ref().and_then(|m| m.map.get(&key).cloned()));
    if let Some(c) = hit.filter(|c| RULE_BUDGET.with(|b| b.get()) >= c.steps) {
        RULE_BUDGET.with(|b| b.set(b.get() - c.steps));
        MACHINE_FALLBACKS.with(|f| f.set(f.get() + c.fallbacks));
        RULE_TRACE.with(|tr| {
            if let Some(v) = tr.borrow_mut().as_mut() {
                v.extend(c.trace.iter().cloned());
            }
        });
        return c.out.clone();
    }
    let (budget0, fallbacks0, trace0) = (RULE_BUDGET.with(|b| b.get()), MACHINE_FALLBACKS.with(|f| f.get()), RULE_TRACE.with(|tr| tr.borrow().as_ref().map(|v| v.len())));
    let cuts0 = CYCLE_CUTS.with(|c| c.get());
    let out = rewrite_uncached(t, n, k);
    let budget1 = RULE_BUDGET.with(|b| b.get());
    // a call that ran the budget out was cut short by it: its result depends on the budget it started with; one with a cycle cut
    // depends on the terms being rewritten further out
    if budget1 > 0 && CYCLE_CUTS.with(|c| c.get()) == cuts0 {
        let trace = RULE_TRACE.with(|tr| tr.borrow().as_ref().map(|v| v[trace0.unwrap_or(0)..].to_vec()).unwrap_or_default());
        let entry = Rewritten { out: out.clone(), steps: budget0 - budget1, fallbacks: MACHINE_FALLBACKS.with(|f| f.get()) - fallbacks0, trace, traced: trace0.is_some() };
        REWRITE_MEMO.with(|m| {
            if let Some(m) = m.borrow_mut().as_mut() {
                m.map.insert(key, std::rc::Rc::new(entry));
            }
        });
    }
    out
}

fn rewrite_uncached(t: &Term, n: usize, k: usize) -> (Term, PlanRc) {
    let Term::Op(o, a, b) = t else { return (t.clone(), Plan::refl(t)) };
    // children first: trying the library rules on a node before its children are normalized raised M 3x (docs/tier-cycle.md, "Rule order")
    let ((a2, pa), (b2, pb)) = (rewrite(a, n, k), rewrite(b, n, k));
    let cong = Plan::cong(*o, pa, pb);
    let t1 = Term::Op(*o, Box::new(a2.clone()), Box::new(b2.clone()));
    if *o != ADD {
        // the library rules first (`shldist`, ...)
        if let Some((target, step)) = rule_step(&t1) {
            let (t3, p3) = rewrite(&target, n, k);
            return (t3, Plan::trans(Plan::trans(cong, step), p3));
        }
        if *o == SUB {
            // a difference: then the carry-encoding search
            return match tree_step(n, &t1, k) {
                Some((target, law)) => (target, Plan::trans(cong, law)),
                None => (t1, cong),
            };
        }
        if matches!(*o, LT | SHL1 | SHR1) {
            return (t1, cong);
        }
        // bitwise and shift terms only: a node equal to 0, -1 or one of its own subterms collapses to it, by the
        // per-position prover (the truth-table collapse below treats a shift as an atom)
        if let (false, true, true) = (ablated("collapse"), t1.add_free(), t1.has_shift()) {
            let mut subs = vec![];
            t1.subterms(&mut subs);
            let cands = [Term::Zero, Term::Ones].into_iter().chain(subs.into_iter().skip(1).filter(|c| c.size() < t1.size()));
            if let Some(c) = cands.into_iter().find(|c| c.add_free() && t1.is_law(c, k)) {
                return (c.clone(), Plan::trans(cong, Plan::law(LawKind::Bitwise, t1.clone(), c, vars(k))));
            }
        }
        // a bitwise node equal to 0, -1 or one of its atoms collapses to it (truth table, then `bitwise_law`)
        let mut atoms = vec![];
        if let (false, Some(abs)) = (ablated("collapse"), abstract_atoms(&t1, &mut atoms, k)) {
            let truth = |t: &Term| (0..1usize << k).map(|m| term_gb(&Bools, t, &(0..k).map(|v| m >> v & 1 == 1).collect::<Vec<_>>())).collect::<Vec<_>>();
            let want = truth(&abs);
            let cands: Vec<Term> = [Term::Zero, Term::Ones].into_iter().chain((0..k).map(Term::V)).collect();
            if let Some(c) = cands.iter().find(|c| c.max_var() < atoms.len().max(1) && truth(c) == want) {
                let target = if let Term::V(i) = c { atoms[*i].clone() } else { c.clone() };
                if target != t1 {
                    let args = (0..k).map(|i| atoms.get(i).cloned().unwrap_or(Term::V(0))).collect();
                    return (target, Plan::trans(cong, Plan::law(LawKind::Bitwise, abs, c.clone(), args)));
                }
            }
        }
        // commutative operands in a fixed order (text order, constants last: 0 before -1), by the generic bitwise law
        let constant = |t: &Term| match t {
            Term::Zero => Some(0),
            Term::Ones => Some(1),
            _ => None,
        };
        let before = match (constant(&b2), constant(&a2)) {
            (None, None) => b2.show_cmp(&a2).is_lt(),
            (None, Some(_)) => true,
            (Some(_), None) => false,
            (Some(cb), Some(ca)) => cb < ca,
        };
        if before {
            let swap = |x: Term, y: Term| Term::Op(*o, Box::new(x), Box::new(y));
            let law = Plan::law(LawKind::Bitwise, swap(Term::V(0), Term::V(1)), swap(Term::V(1), Term::V(0)), vec![a2.clone(), b2.clone()]);
            return (swap(b2, a2), Plan::trans(cong, law));
        }
        return (t1, cong);
    }
    let sum = |p: &Term, q: &Term| Term::Op(ADD, Box::new(p.clone()), Box::new(q.clone()));
    let (x, y, z) = (Term::V(0), Term::V(1), Term::V(2));
    let assoc = |p: &Term, q: &Term, r: &Term| Plan::law(LawKind::Assoc, sum(&sum(&x, &y), &z), sum(&x, &sum(&y, &z)), vec![p.clone(), q.clone(), r.clone()]);
    let comm = |p: &Term, q: &Term| Plan::law(LawKind::Comm, sum(&x, &y), sum(&y, &x), vec![p.clone(), q.clone()]);
    // `x + 0` and `x + ~x` are constant-carry sums (`chain_step`); steps of their own were removed as redundant
    let step = if let Some(r) = rule_step(&t1) {
        Some(r)
    } else if let Some(r) = chain_step(&a2, &b2) {
        Some(r)
    } else if let Some(r) = tree_step(n, &t1, k) {
        Some(r)
    } else if let (false, Term::Op(ADD, p, q)) = (ablated("assoc"), &a2) {
        // (p + q) + r = p + (q + r)
        Some((sum(p, &sum(q, &b2)), assoc(p, q, &b2)))
    } else if let (false, Term::Op(ADD, bp, bq)) = (ablated("assoc") || ablated("comm"), &b2) {
        if bp.show_cmp(&a2).is_lt() {
            // a + (b + c) = (a + b) + c = (b + a) + c = b + (a + c)
            let (a_, b_, c_) = (&a2, &**bp, &**bq);
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
    match t {
        Term::Zero | Term::Ones => Some(t.clone()),
        Term::V(_) | Term::Op(ADD | SUB | SHL1 | SHR1, ..) => {
            let i = match atoms.iter().position(|a| a == t) {
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

/// `t` with every occurrence of the subterm `x` replaced by `with`.
pub fn replace_term(t: &Term, x: &Term, with: &Term) -> Term {
    if t == x {
        return with.clone();
    }
    match t {
        Term::Op(o, a, b) => Term::Op(*o, Box::new(replace_term(a, x, with)), Box::new(replace_term(b, x, with))),
        _ => t.clone(),
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
            let args = (0..k).map(|i| atoms.get(i).cloned().unwrap_or(Term::V(0))).collect();
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
            return Some(Plan::law(LawKind::Bitwise, a.clone(), b.clone(), vars(k)));
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
    if screened && a.counterexample_in(b, n, k, 16).is_some() || !screened && tree_encoding(n, k, a, b).is_none() {
        return None;
    }
    MACHINE_FALLBACKS.with(|c| c.set(c.get() + 1));
    Some(Plan::law(LawKind::Tree, a.clone(), b.clone(), vars(k)))
}

/// `shr1 A = shr1 B` (or `0 = shr1 B`, as `shr1 0`) for machine-expressible `A`, `B`, without a lookahead machine: the
/// bit-0 mask law `shr1 t = shr1 (t & M)`, `M = shl1 -1`, turns the pair into the shift-free law `A & M = B & M`
/// (search note section 47).
pub fn shr_mask_eq(n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    let shr = |t: &Term| Term::Op(SHR1, Box::new(t.clone()), Box::new(Term::Zero));
    let (mask, one_arg) = (Term::Op(SHL1, Box::new(Term::Ones), Box::new(Term::Zero)), |t: &Term| match t {
        Term::Op(SHR1, x, _) if Machine::parse(x).is_some() => Some((**x).clone()),
        Term::Zero => Some(Term::Zero),
        _ => None,
    });
    if ablated("shrmask") || !matches!(a, Term::Op(SHR1, ..)) && !matches!(b, Term::Op(SHR1, ..)) {
        return None;
    }
    let (x, y) = (one_arg(a)?, one_arg(b)?);
    // the pair `A & M`, `B & M`: rewrite both, close with `prove_eq` (a machine law when they stay arithmetic)
    let (ta, tb) = (Term::Op(AND, Box::new(x.clone()), Box::new(mask.clone())), Term::Op(AND, Box::new(y.clone()), Box::new(mask.clone())));
    let ((r1, p1), (r2, p2)) = (rewrite(&ta, n, k), rewrite(&tb, n, k));
    let mid = prove_eq(n, k, &r1, &r2)?;
    let cong = Plan::cong(SHR1, Plan::trans(p1, Plan::trans(mid, Plan::sym(p2))), Plan::refl(&Term::Zero));
    // `a = shr1 (A & M)` and `b = shr1 (B & M)`
    let side_proof = |orig: &Term, arg: &Term| -> Option<PlanRc> {
        if matches!(orig, Term::Zero) {
            // `0 = shr1 0 = shr1 (0 & M)`: the second step is a congruence on `0 = 0 & M` by the rewriter
            let (r, pr) = rewrite(&Term::Op(AND, Box::new(Term::Zero), Box::new(mask.clone())), n, k);
            if r != Term::Zero {
                return None;
            }
            let (target, step) = rule_step(&shr(&Term::Zero))?;
            if target != Term::Zero {
                return None;
            }
            Some(Plan::trans(Plan::sym(step), Plan::cong(SHR1, Plan::sym(pr), Plan::refl(&Term::Zero))))
        } else {
            Some(Plan::law(LawKind::Rule("shrmask"), shr(&Term::V(0)), shr(&Term::Op(AND, Box::new(Term::V(0)), Box::new(mask.clone()))), vec![arg.clone()]))
        }
    };
    let (pa, pb) = (side_proof(a, &x)?, side_proof(b, &y)?);
    Some(Plan::trans(Plan::trans(pa, cong), Plan::sym(pb)))
}

/// The plan of `t1 = t2` over `k` variables: both sides rewritten, then closed with `prove_eq`; `None` when that cannot.
pub fn rewrite_plan(n: usize, k: usize, t1: &Term, t2: &Term) -> Option<PlanRc> {
    // an `lt` root (a one-bit result) is rewritten under its operands, then closed by congruence or, failing that,
    // by the `lt` machine proof for the rewritten pair; `lt` occurs only at the root
    let lt_roots = matches!((t1, t2), (Term::Op(LT, ..), Term::Op(LT, ..)));
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
            let by_operands = if let (Term::Op(LT, a2, b2), Term::Op(LT, c2, d2)) = (&r1, &r2) {
                match (prove_eq(n, k, a2, c2), prove_eq(n, k, b2, d2)) {
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
    let root = if matches!((t1, t2), (Term::Op(LT, ..), Term::Op(LT, ..))) { bv_ty(1) } else { bv.clone() };
    let (mut proof, mut stmt) = (c.proof(plan).2, id(root, c.ev(t1), c.ev(t2)));
    for _ in 0..k {
        let g = app(good_bv(n), var(k as u32 - 1));
        (proof, stmt) = (lam(g.clone(), proof), pi(g, stmt));
    }
    for _ in 0..k {
        (proof, stmt) = (lam(bv.clone(), proof), pi(bv.clone(), stmt));
    }
    (proof, stmt)
}

/// One law per kind of step (assoc and comm, a rule, a constant carry, the carry-encoding search, a collapse, an `lt` root, the
/// bit-0 mask): the plan is the same while counting (`SCORE_ONLY`) as while proving, its sides are the law's, and it compiles to
/// a proof the kernel accepts.
#[test]
fn plans_compile_to_checked_proofs() {
    tatic::kernel::scoped(|| {
        let (v, z, ones) = (Term::V, Term::Zero, Term::Ones);
        let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
        let shr = |a: Term| op(SHR1, a, Term::Zero);
        let laws = [
            (op(ADD, op(ADD, v(2), v(0)), v(1)), op(ADD, v(1), op(ADD, v(0), v(2)))),
            (op(SHL1, op(AND, v(0), v(1)), z.clone()), op(AND, op(SHL1, v(0), z.clone()), op(SHL1, v(1), z.clone()))),
            (op(ADD, v(0), op(XOR, v(0), ones.clone())), ones.clone()),
            (op(SUB, ones.clone(), v(1)), op(XOR, v(1), ones.clone())),
            (op(OR, v(0), op(AND, v(0), v(1))), v(0)),
            (op(LT, v(0), op(ADD, v(1), z.clone())), op(LT, v(0), v(1))),
            (shr(op(ADD, v(0), v(0))), shr(op(SUB, op(ADD, v(0), v(0)), ones.clone()))),
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
            assert!(sides[0] == sides[1] && sides[0] == (l.clone(), r.clone()), "{} = {}", l.show(), r.show());
            let (p, s) = law_proof(4, k, l, r, &plans[0]);
            ck(&format!("{} = {}", l.show(), r.show()), &p, &s);
        }
    })
}

#[test]
pub fn laws_over_three_vectors_check_and_false_ones_fail() {
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::V(i);
        let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
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

#[test]
pub fn a_law_over_lemma_parameters_discharges_to_a_closed_proof() {
    tatic::kernel::scoped(|| {
        let v = |i: usize| Term::V(i);
        let op = |o: usize, a: Term, b: Term| Term::Op(o, Box::new(a), Box::new(b));
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
        let all = apps(lam(sm.clone(), lam(shift(&s, 0, 1), lam(shift(&sr, 0, 2), var(2)))), vec![pm, p, pr]);
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
        EXTRA_RULES.with(|e| e.borrow_mut().clear());
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
        EXTRA_RULES.with(|e| e.borrow_mut().clear());
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
/// traces that rule's left side matches nowhere; the rule miner seeds each candidate's scoring with them. The whole memo would replay
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
        EXTRA_RULES.with(|e| e.borrow_mut().clear());
        RULE_BUDGET.with(|b| b.set(i64::MAX / 2));
        (out, REWRITE_MEMO.with(|m| m.borrow_mut().take()).unwrap())
    };
    let (_, memo) = run(&base, RewriteMemo::new(kv));
    for extra in ["sub(sub(x, y), z) -> sub(x, add(y, z))\n", "or(x, and(x, y)) -> x\n"] {
        let rules: Vec<(Term, Term)> = base.iter().cloned().chain(parse_rules(extra)).collect();
        let l = &rules.last().unwrap().0;
        let seed = memo.filtered(|tr| !tr.iter().any(|t| match_pat(l, t, &mut vec![None; 8])));
        assert!(!seed.map.is_empty() && seed.map.len() < memo.map.len(), "{extra}: the filter kept {} of {}", seed.map.len(), memo.map.len());
        let fresh = run(&rules, RewriteMemo::new(kv)).0;
        assert_eq!(run(&rules, seed).0, fresh, "{extra}");
        assert_ne!(run(&rules, memo.filtered(|_| true)).0, fresh, "{extra}: the extra rule changes nothing here");
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
