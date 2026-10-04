// A fixed-width bit-vector as a Church-encoded n-ary tuple of Church Bools, with an
// unrolled ripple-carry `add`, on the unchanged kernel (public API only).
use std::time::Instant;
use tatic::kernel::*;

mod encoding;
mod rewrite;
mod machine;
mod search;
#[allow(unused_imports)]
use encoding::*;
#[allow(unused_imports)]
use rewrite::*;
#[allow(unused_imports)]
use machine::*;
#[allow(unused_imports)]
use search::*;

type BitPair = (Vec<Expr>, Vec<Expr>);
type BitTriple = (Vec<Expr>, Vec<Expr>, Vec<Expr>);
/// Output bits of a circuit from the two operands' bits.
type BitsDyn = dyn Fn(&[Expr], &[Expr]) -> Vec<Expr>;
type Bits4<'a> = &'a dyn Fn(&[Expr], &[Expr], &[Expr], &[Expr]) -> BitPair;
type DdBuild<'a> = &'a dyn Fn(&DdGates, &[Sig]) -> (Sig, Sig);
/// A rule candidate's score: (gain, (lhs, rhs), per-law outcomes, cost).
type ScoredRule = (i64, (Term, Term), Vec<bool>, i64);

// The allocator `main.rs` ships with: the lib's own `#[global_allocator]` is
// `#[cfg(test)]`, so without this these timings ran on the system heap.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
