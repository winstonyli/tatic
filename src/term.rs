//! Content-addressed term store for a small higher-order language.
//!
//! Every term is identified by the BLAKE3 hash of its structure, so two
//! independently-built terms that are syntactically identical always share
//! one hash. That hash doubles as the cache key the JIT engine uses to
//! recognize "this exact transformation again" without re-inspecting the
//! term graph.

use cranelift_entity::{PrimaryMap, entity_impl};
use hashbrown::HashMap;

pub type Hash = blake3::Hash;

/// A `Hasher` for `HashMap`s keyed by [`Hash`] (or a tuple/struct
/// containing one) -- `Hash` is already a uniformly-random 32-byte BLAKE3
/// digest, so hashing it *again* through the default SipHash-based
/// hasher on every lookup is pure waste, and a measured one: profiling
/// `over_application_instance_proof` (a representative proof-construction
/// benchmark) under callgrind found SipHash on `Hash`-keyed maps
/// (`TermStore::by_hash`'s own interning table foremost, plus
/// `ClosurePostulates`'s several memoization tables) accounting for over
/// 40% of all instructions retired -- more than everything else in the
/// entire proof-construction pipeline combined. This is the standard
/// "don't re-hash an already-good hash" fix (the same reasoning
/// `rustc-hash`/`FxHash` is built on): fold each `write`n chunk into the
/// running state with a cheap rotate-xor-multiply instead of SipHash's
/// several-round mixing, fast enough that hashing a `Hash`'s own 32 bytes
/// costs a handful of instructions instead of dozens. Not
/// cryptographically strong and not DoS-resistant -- fine here, since
/// every key either already came from a cryptographic hash (blake3) or
/// is small, internal, compiler-generated data, never adversarial input.
#[derive(Default, Clone, Copy)]
pub struct FxHasher(u64);

impl std::hash::Hasher for FxHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        const SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;
        let mut state = self.0;
        for chunk in bytes.chunks(8) {
            let mut buf = [0u8; 8];
            buf[..chunk.len()].copy_from_slice(chunk);
            let word = u64::from_ne_bytes(buf);
            state = (state.rotate_left(5) ^ word).wrapping_mul(SEED);
        }
        self.0 = state;
    }
}

/// `BuildHasher` for [`FxHasher`] -- the third type parameter both
/// `std::collections::HashMap` and `hashbrown::HashMap` accept, so this
/// one definition works for either, wherever a map is keyed by [`Hash`].
pub type FxBuildHasher = std::hash::BuildHasherDefault<FxHasher>;

/// Dense index into a [`TermStore`], used for internal storage/traversal.
/// Content identity is still the [`Hash`]; this is just cheap plumbing.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TermId(u32);
entity_impl!(TermId, "term");

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum PrimOp {
    Add = 0,
    Sub = 1,
    Mul = 2,
    Div = 3,
    Mod = 4,
    Lt = 5,
    Le = 6,
    Eq = 7,
}

/// A node in the term graph. Children are referenced by content hash, not
/// by pointer, so structurally-equal subterms are automatically shared.
///
/// - `Var(i)` is a de Bruijn index (0 = innermost binder).
/// - `Abs(body)` is a plain (non-recursive) lambda.
/// - `Rec(inner)` ties a knot: within `inner`'s scope, one extra outer
///   variable slot is bound to the whole `Rec` term itself, giving direct
///   self-recursion (`inner` is typically an `Abs`-chain, one `Abs` per
///   parameter, with the innermost body allowed to call back through that
///   extra slot).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Term {
    Var(u32),
    Lit(i64),
    Prim(PrimOp, Hash, Hash),
    If(Hash, Hash, Hash),
    Abs(Hash),
    App(Hash, Hash),
    Rec(Hash),
}

impl Term {
    fn write_bytes(&self, buf: &mut Vec<u8>) {
        match self {
            Term::Var(i) => {
                buf.push(0);
                buf.extend_from_slice(&i.to_le_bytes());
            }
            Term::Lit(n) => {
                buf.push(1);
                buf.extend_from_slice(&n.to_le_bytes());
            }
            Term::Prim(op, a, b) => {
                buf.push(2);
                buf.push(*op as u8);
                buf.extend_from_slice(a.as_bytes());
                buf.extend_from_slice(b.as_bytes());
            }
            Term::If(c, t, e) => {
                buf.push(3);
                buf.extend_from_slice(c.as_bytes());
                buf.extend_from_slice(t.as_bytes());
                buf.extend_from_slice(e.as_bytes());
            }
            Term::Abs(body) => {
                buf.push(4);
                buf.extend_from_slice(body.as_bytes());
            }
            Term::App(f, a) => {
                buf.push(5);
                buf.extend_from_slice(f.as_bytes());
                buf.extend_from_slice(a.as_bytes());
            }
            Term::Rec(inner) => {
                buf.push(6);
                buf.extend_from_slice(inner.as_bytes());
            }
        }
    }

    fn content_hash(&self) -> Hash {
        let mut buf = Vec::with_capacity(64);
        self.write_bytes(&mut buf);
        blake3::hash(&buf)
    }
}

/// Hash-consing store: interns [`Term`] nodes and lets callers resolve a
/// content [`Hash`] back to its [`Term`].
#[derive(Default)]
pub struct TermStore {
    terms: PrimaryMap<TermId, Term>,
    hashes: PrimaryMap<TermId, Hash>,
    by_hash: HashMap<Hash, TermId, FxBuildHasher>,
}

impl TermStore {
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a term, returning its content hash. Structurally identical
    /// terms are deduplicated and share storage.
    pub fn intern(&mut self, term: Term) -> Hash {
        let hash = term.content_hash();
        if let Some(id) = self.by_hash.get(&hash) {
            debug_assert_eq!(self.terms[*id], term, "blake3 collision or bug");
            return hash;
        }
        let id = self.terms.push(term);
        let id2 = self.hashes.push(hash);
        debug_assert_eq!(id, id2);
        self.by_hash.insert(hash, id);
        hash
    }

    pub fn resolve(&self, hash: Hash) -> &Term {
        let id = self
            .by_hash
            .get(&hash)
            .expect("term hash not present in this store");
        &self.terms[*id]
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    // --- convenience builders -------------------------------------------

    pub fn var(&mut self, i: u32) -> Hash {
        self.intern(Term::Var(i))
    }

    pub fn lit(&mut self, n: i64) -> Hash {
        self.intern(Term::Lit(n))
    }

    pub fn prim(&mut self, op: PrimOp, a: Hash, b: Hash) -> Hash {
        self.intern(Term::Prim(op, a, b))
    }

    pub fn if_(&mut self, c: Hash, t: Hash, e: Hash) -> Hash {
        self.intern(Term::If(c, t, e))
    }

    pub fn abs(&mut self, body: Hash) -> Hash {
        self.intern(Term::Abs(body))
    }

    pub fn app(&mut self, f: Hash, a: Hash) -> Hash {
        self.intern(Term::App(f, a))
    }

    /// `f a b`, i.e. `(f a) b`.
    pub fn app2(&mut self, f: Hash, a: Hash, b: Hash) -> Hash {
        let fa = self.app(f, a);
        self.app(fa, b)
    }

    pub fn rec(&mut self, inner: Hash) -> Hash {
        self.intern(Term::Rec(inner))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structurally_identical_terms_share_a_hash() {
        let mut a = TermStore::new();
        let mut b = TermStore::new();

        let one_a = a.lit(1);
        let two_a = a.lit(2);
        let sum_a = a.prim(PrimOp::Add, one_a, two_a);

        // Build the exact same term independently, in a different store.
        let two_b = b.lit(2);
        let one_b = b.lit(1);
        let sum_b = b.prim(PrimOp::Add, one_b, two_b);

        assert_eq!(sum_a, sum_b);
    }

    #[test]
    fn interning_deduplicates_within_a_store() {
        let mut s = TermStore::new();
        let before = s.len();
        let h1 = s.lit(42);
        let h2 = s.lit(42);
        assert_eq!(h1, h2);
        assert_eq!(s.len(), before + 1);
    }

    #[test]
    fn distinct_terms_get_distinct_hashes() {
        let mut s = TermStore::new();
        let a = s.lit(1);
        let b = s.lit(2);
        assert_ne!(a, b);
    }
}
