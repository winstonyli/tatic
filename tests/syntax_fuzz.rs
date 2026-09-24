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
//! that accepts a possibly-malformed term). Negative literals *are*
//! generated, in every position: this grammar has no negative-literal
//! syntax, only subtraction, so the documented contract for a directly
//! built `Lit(n)` with `n < 0` is that it reparses to the desugared
//! `Prim(Sub, Lit(0), Lit(-n))` -- semantically equal, not hash-equal
//! (`syntax.rs`'s own `a_directly_built_negative_literal_does_not_round_trip_exactly`).
//! The check compares against `desugar_negative_lits(h)` rather than `h`,
//! so it still demands exact hash equality everywhere else, and would catch
//! `print` emitting a bare `-n` where unary minus binds differently (e.g.
//! `f -2`, which reparses as the subtraction `f - 2`).
//!
//! Deterministic (the same tiny splitmix64 PRNG `compile_fuzz.rs`/
//! `kernel_fuzz.rs` use), seed-scanned, bounded generation depth.

use tatic::syntax::{parse, print};
use tatic::term::{Hash, PrimOp, Term, TermStore};

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
        s.lit(rng.i64_range(-MAX_LIT, MAX_LIT))
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

/// `h` with every negative `Lit(n)` replaced by `Prim(Sub, Lit(0), Lit(-n))`
/// -- what `parse` itself produces for the text `-n` (see module docs).
fn desugar_negative_lits(s: &mut TermStore, h: Hash) -> Hash {
    match s.resolve(h).clone() {
        Term::Var(_) => h,
        Term::Lit(n) if n < 0 => {
            let zero = s.lit(0);
            let pos = s.lit(-n);
            s.prim(PrimOp::Sub, zero, pos)
        }
        Term::Lit(_) => h,
        Term::Prim(op, a, b) => {
            let (a, b) = (desugar_negative_lits(s, a), desugar_negative_lits(s, b));
            s.prim(op, a, b)
        }
        Term::If(c, t, e) => {
            let (c, t, e) = (desugar_negative_lits(s, c), desugar_negative_lits(s, t), desugar_negative_lits(s, e));
            s.if_(c, t, e)
        }
        Term::Abs(b) => {
            let b = desugar_negative_lits(s, b);
            s.abs(b)
        }
        Term::App(f, a) => {
            let (f, a) = (desugar_negative_lits(s, f), desugar_negative_lits(s, a));
            s.app(f, a)
        }
        Term::Rec(i) => {
            let i = desugar_negative_lits(s, i);
            s.rec(i)
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

        let expected = desugar_negative_lits(&mut s, h);

        let text = print(&s, h);
        let mut fresh = TermStore::new();
        let reparsed = parse(&mut fresh, &text)
            .unwrap_or_else(|e| panic!("seed={seed}: printed text failed to reparse: {text:?}\nerror: {e}"));
        assert_eq!(reparsed, expected, "seed={seed}: round-trip mismatch; printed: {text:?}");
    }
}
