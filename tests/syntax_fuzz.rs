//! Fuzzes `syntax.rs`'s own round-trip property directly: `parse(print(h))
//! == h` (exact content-hash equality, not just semantic equivalence) for
//! a random, well-scoped term. `syntax.rs`'s own hand-written tests already
//! cover a handful of hand-picked precedence traps (a right-nested
//! subtraction a left-associative parser would never itself produce, a
//! nested comparison, an application argument that's itself an
//! application) -- each one added because a *plausible* case turned out to
//! need parentheses `print`'s precedence logic could get wrong. This
//! generates many more such shapes than anyone would think to hand-pick,
//! across every constructor (`Prim` with all eight operators, `If`, `Abs`,
//! `App`, `Rec` of random arity), with random right/left nesting.
//!
//! Deliberately stays inside `print`'s own documented contract: every
//! generated `Var` is genuinely bound by an enclosing binder (`print`
//! isn't written to handle an out-of-scope one -- it isn't a `Result`-
//! returning function at all, unlike every other place in this codebase
//! that accepts a possibly-malformed term). Literals range over both
//! signs, plus the `i64::MIN`/`i64::MAX` extremes, in every position -- a
//! negative one prints as unary minus, which must be parenthesised as an
//! application's function or argument (`f -2` reparses as `f - 2`) and
//! must fold back into the same `Lit` (`i64::MIN`'s magnitude alone is out
//! of range).
//!
//! Deterministic (the same tiny splitmix64 PRNG `compile_fuzz.rs`/
//! `kernel_fuzz.rs` use), seed-scanned, bounded generation depth.

use tatic::syntax::{parse, print};
use tatic::term::{Hash, PrimOp, TermStore};

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u32) -> u32 {
        (self.next_u64() % n as u64) as u32
    }

    fn i64_range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next_u64() % ((hi - lo + 1) as u64)) as i64
    }
}

const MAX_LIT: i64 = 50;
const MAX_DEPTH: u32 = 6;

fn random_prim_op(rng: &mut Rng) -> PrimOp {
    use PrimOp::*;
    [Add, Sub, Mul, Div, Mod, Lt, Le, Eq][rng.below(8) as usize]
}

fn gen_leaf(rng: &mut Rng, s: &mut TermStore, scope: u32) -> Hash {
    if scope > 0 && rng.below(2) == 0 {
        s.var(rng.below(scope))
    } else {
        let n = match rng.below(20) {
            0 => i64::MIN,
            1 => i64::MAX,
            _ => rng.i64_range(-MAX_LIT, MAX_LIT),
        };
        s.lit(n)
    }
}

/// `scope` is how many binders currently enclose the term being built, so
/// every `Var` this ever generates (via `gen_leaf`) is genuinely bound --
/// `print` isn't exercised outside its own documented contract.
fn gen_term(rng: &mut Rng, s: &mut TermStore, scope: u32, fuel: u32) -> Hash {
    if fuel == 0 || rng.below(3) == 0 {
        return gen_leaf(rng, s, scope);
    }
    let f = fuel - 1;
    match rng.below(5) {
        0 => {
            let op = random_prim_op(rng);
            let a = gen_term(rng, s, scope, f);
            let b = gen_term(rng, s, scope, f);
            s.prim(op, a, b)
        }
        1 => {
            let c = gen_term(rng, s, scope, f);
            let t = gen_term(rng, s, scope, f);
            let e = gen_term(rng, s, scope, f);
            s.if_(c, t, e)
        }
        2 => {
            let body = gen_term(rng, s, scope + 1, f);
            s.abs(body)
        }
        3 => {
            let func = gen_term(rng, s, scope, f);
            let arg = gen_term(rng, s, scope, f);
            s.app(func, arg)
        }
        _ => {
            let arity = rng.below(3); // 0, 1, or 2 -- matches round_trips_a_zero_arity_rec's own concern
            let body = gen_term(rng, s, scope + arity + 1, f); // +1 self, +arity params
            let mut inner = body;
            for _ in 0..arity {
                inner = s.abs(inner);
            }
            s.rec(inner)
        }
    }
}

#[test]
fn syntax_round_trips_random_terms() {
    const SEEDS: u64 = 3000;
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x5117_AC7A_u64 ^ seed);
        let mut s = TermStore::new();
        let h = gen_term(&mut rng, &mut s, 0, MAX_DEPTH);

        let text = print(&s, h);
        let mut fresh = TermStore::new();
        let reparsed = parse(&mut fresh, &text)
            .unwrap_or_else(|e| panic!("seed={seed}: printed text failed to reparse: {text:?}\nerror: {e}"));
        assert_eq!(reparsed, h, "seed={seed}: round-trip mismatch; printed: {text:?}");
    }
}
