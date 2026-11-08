use super::*;

/// A multiply-rotate hasher (the kernel's `PtrHasher` scheme) for the memos' small keys.
#[derive(Default)]
pub struct Fx(u64);
impl std::hash::Hasher for Fx {
    fn finish(&self) -> u64 {
        self.0.rotate_left(26)
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.write_usize(*b as usize);
        }
    }
    fn write_usize(&mut self, x: usize) {
        self.0 = (self.0.rotate_left(5) ^ x as u64).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
}

/// A builder memo: one thread's values by key, for the current interning generation (`intern_generation`).
pub type GenMemo<K, V> = std::cell::RefCell<(u32, std::collections::HashMap<K, V, std::hash::BuildHasherDefault<Fx>>)>;

/// `build()` once per key, interning generation and thread. A term built in one generation is not canonical in the
/// next, so the memo empties when the generation changes; rebuilding re-interns every node, which is what it saves.
pub fn gen_memo<K: std::hash::Hash + Eq, V: Clone>(memo: &'static std::thread::LocalKey<GenMemo<K, V>>, key: K, build: impl FnOnce(&K) -> V) -> V {
    let g = tatic_kernel::intern_generation();
    let hit = memo.with(|c| {
        let mut c = c.borrow_mut();
        if c.0 != g {
            *c = (g, Default::default());
        }
        c.1.get(&key).cloned()
    });
    // built outside the borrow: a builder may use the same memo (a gate constant uses other constants)
    hit.unwrap_or_else(|| {
        let v = build(&key);
        memo.with(|c| c.borrow_mut().1.insert(key, v.clone()));
        v
    })
}

/// The closed constant `build` makes, built once per generation and keyed by the function's address: the machine proofs
/// use the gates millions of times. A function with two addresses (two codegen units) only builds an equal term twice.
pub fn constant(build: fn() -> Expr) -> Expr {
    thread_local! {
        static CONSTANTS: GenMemo<usize, Expr> = Default::default();
    }
    gen_memo(&CONSTANTS, build as usize, |_| build())
}

/// `Pi C. C -> C -> C`, written without `arrow`: its codomain shift ran at every call, and building the motives of the
/// case-tree lemmas calls this millions of times.
pub fn bool0() -> Expr {
    constant(|| pi(sort(0), pi(var(0), pi(var(1), var(2)))))
}
pub fn t() -> Expr {
    constant(|| lam(sort(0), lam(var(0), lam(var(1), var(1)))))
}
pub fn f() -> Expr {
    constant(|| lam(sort(0), lam(var(0), lam(var(1), var(0)))))
}
pub fn bit(b: bool) -> Expr {
    if b { t() } else { f() }
}
pub fn bool2(body: Expr) -> Expr {
    // \a b : Bool0. \C t f. body   ctx [a,b,C,t,f]: f=0 t=1 C=2 b=3 a=4
    lam(bool0(), lam(bool0(), lam(sort(0), lam(var(0), lam(var(1), body)))))
}
pub fn and_() -> Expr {
    constant(|| bool2(app3(var(4), var(2), app3(var(3), var(2), var(1), var(0)), var(0))))
}
pub fn or_() -> Expr {
    constant(|| bool2(app3(var(4), var(2), var(1), app3(var(3), var(2), var(1), var(0)))))
}
pub fn xor_() -> Expr {
    constant(|| bool2(app3(var(4), var(2), app3(var(3), var(2), var(0), var(1)), app3(var(3), var(2), var(1), var(0)))))
}
pub fn and(a: Expr, b: Expr) -> Expr { app2(and_(), a, b) }
pub fn or(a: Expr, b: Expr) -> Expr { app2(or_(), a, b) }
pub fn xor(a: Expr, b: Expr) -> Expr { app2(xor_(), a, b) }

/// The `n` low bits set (`n` up to 128).
pub fn low_bits(n: usize) -> u128 {
    if n >= 128 { u128::MAX } else { (1u128 << n) - 1 }
}

/// Bool0 -> ... -> Bool0 -> C (n arrows), in a context whose top variable is C.
pub fn karrow(n: usize) -> Expr {
    if n == 0 { var(0) } else { arrow(bool0(), karrow(n - 1)) }
}
pub fn bv_ty(n: usize) -> Expr {
    pi(sort(1), arrow(karrow(n), var(0)))
}
pub fn apps(mut f: Expr, args: Vec<Expr>) -> Expr {
    for a in args {
        f = app(f, a);
    }
    f
}
/// Wraps `body` in the `2n` binders every n-bit law proof opens with: `n` Bool binders, then `n` `good_bool` hypotheses on them.
pub fn binders(n: usize, mut body: Expr) -> Expr {
    for _ in 0..n {
        body = lam(app(good_bool(), var(n as u32 - 1)), body);
    }
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    body
}
/// `\b_0..b_(n-1). \C k. k b_0 .. b_(n-1)`: the vector built from `n` bits (context `[b.., C, k]`: `k` = var 0, `b_i` = var(n+1-i)).
pub fn bits_to_bv(n: usize) -> Expr {
    let mut f = apps(var(0), (0..n).map(|i| var((n + 1 - i) as u32)).collect());
    f = lam(sort(1), lam(karrow(n), f));
    for _ in 0..n {
        f = lam(bool0(), f);
    }
    f
}
/// Literal: \C k. k b0 .. b(n-1), least significant bit first.
pub fn lit(n: usize, v: u128) -> Expr {
    let bits = (0..n).map(|i| bit((v >> i) & 1 == 1)).collect();
    lam(sort(1), lam(karrow(n), apps(var(0), bits)))
}
/// \a b. \C k. a C (\a0..a(n-1). b C (\b0..b(n-1). k s0 .. s(n-1)))  with ripple-carry sums.
pub fn add(n: usize) -> Expr {
    ripple(n, false)
}
/// `a - b` (mod 2^n) as a ripple-borrow chain: the same circuit with the borrow `maj(~a, b, borrow)` as carry.
pub fn sub(n: usize) -> Expr {
    ripple(n, true)
}
/// `lt_u a b` as a one-bit vector (a `Bool0` result would live one universe below the claims about it): the final
/// borrow of the ripple-borrow chain of `a - b`, set iff `a < b` as unsigned numbers.
pub fn lt_u(n: usize) -> Expr {
    let d = 4 + 2 * n; // depth at the innermost body: a b C k a0.. b0..
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let mut carry = f();
    for i in 0..n {
        let (a, b) = (v(4 + i), v(4 + n + i));
        carry = ripple_carry(true, a, b, carry, xor(a, b));
    }
    let mut body = app(v(3), carry);
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    let outer = app2(var(3), var(1), inner);
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(1), outer))))
}
/// The next carry (or borrow) of one position, given its operand bits, the incoming carry and `x = a ^ b`.
pub fn ripple_carry(sub: bool, a: Expr, b: Expr, c: Expr, x: Expr) -> Expr {
    if sub {
        let na = xor(a, t());
        or(and(na, b), and(c, xor(na, b)))
    } else {
        or(and(a, b), and(c, x))
    }
}
pub fn ripple(n: usize, sub: bool) -> Expr {
    let d = 4 + 2 * n; // depth at the innermost body: a b C k a0.. b0..
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let k = v(3);
    let ai = |i: usize| v(4 + i);
    let bi = |i: usize| v(4 + n + i);
    let mut carry = f();
    let mut sums = Vec::new();
    for i in 0..n {
        let x = xor(ai(i), bi(i));
        sums.push(xor(x, carry));
        carry = ripple_carry(sub, ai(i), bi(i), carry, x);
    }
    let mut body = apps(k, sums);
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    // at depth 4 + n (inside a's bits): b = var(n+2), C = var(n+1)
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    // at depth 4: a = var(3), C = var(1)
    let outer = app2(var(3), var(1), inner);
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(n), outer))))
}

/// Like `add`, but each carry is bound once by `(\c. rest) carry_expr`, so the body stays O(n)
/// nodes instead of O(n^2) (a carry used twice per position is otherwise copied by every beta).
pub fn add_shared(n: usize) -> Expr {
    let d0 = 4 + 2 * n; // depth with all of a's and b's bits open
    let a_at = |j: usize, depth: usize| var((depth - 1 - (4 + j)) as u32);
    let b_at = |j: usize, depth: usize| var((depth - 1 - (4 + n + j)) as u32);
    let df = d0 + n.saturating_sub(1); // depth once c_1 .. c_(n-1) are bound
    let carry_at_final = |j: usize| if j == 0 { f() } else { var((n - 1 - j) as u32) };
    let sums = (0..n).map(|i| xor(xor(a_at(i, df), b_at(i, df)), carry_at_final(i))).collect();
    let mut body = apps(var((df - 1 - 3) as u32), sums);
    for i in (0..n.saturating_sub(1)).rev() {
        let depth = d0 + i; // i carries bound so far; c_i is var(0) when i >= 1
        let ci = if i == 0 { f() } else { var(0) };
        let x = xor(a_at(i, depth), b_at(i, depth));
        let e = or(and(a_at(i, depth), b_at(i, depth)), and(ci, x));
        body = app(lam(bool0(), body), e);
    }
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    let outer = app2(var(3), var(1), inner);
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(n), outer))))
}

pub fn is_ok(r: Result<Expr, String>) -> bool {
    match r {
        Ok(_) => true,
        Err(m) => panic!("{}", m.chars().take(300).collect::<String>()),
    }
}


// ---- Circuits over operand bits: `bits_circuit` closes an output-bit function into a word operator (multiplication's
// shift-and-add partial products, `mul_bits`, summed by ripple adders, `add_rows`).

/// `\a b. \C k. a C (\a_i.. b C (\b_i.. k out_0 .. out_(n-1)))` where `outs(a_bits, b_bits)` gives the output bits.
pub fn bits_circuit(n: usize, outs: BitsFn) -> Expr {
    let d = 4 + 2 * n;
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let a: Vec<Expr> = (0..n).map(|i| v(4 + i)).collect();
    let b: Vec<Expr> = (0..n).map(|i| v(4 + n + i)).collect();
    let mut body = apps(v(3), outs(&a, &b));
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(n), app2(var(3), var(1), inner)))))
}

pub fn add_rows(a: &[Expr], b: &[Expr]) -> Vec<Expr> {
    let mut carry = f();
    let mut sums = vec![];
    for i in 0..a.len() {
        let x = xor(a[i], b[i]);
        sums.push(xor(x, carry));
        carry = ripple_carry(false, a[i], b[i], carry, x);
    }
    sums
}

pub type BitsFn<'a> = &'a dyn Fn(&[Expr], &[Expr]) -> Vec<Expr>;

pub fn mul_bits(n: usize, x: &[Expr], y: &[Expr]) -> Vec<Expr> {
    let row = |i: usize| -> Vec<Expr> { (0..n).map(|j| if j < i { f() } else { and(y[i], x[j - i]) }).collect() };
    (1..n).fold(row(0), |acc, i| add_rows(&acc, &row(i)))
}

/// The truth tables of the bitwise gates `and`, `or` and `xor`, beside the gates (church-bv's `OP_INFO` rows use them too).
pub fn and_truth(a: bool, b: bool) -> bool {
    a && b
}
pub fn or_truth(a: bool, b: bool) -> bool {
    a || b
}
pub fn xor_truth(a: bool, b: bool) -> bool {
    a != b
}
