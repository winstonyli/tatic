// A fixed-width bit-vector as a Church-encoded n-ary tuple of Church Bools, with an
// unrolled ripple-carry `add`, on the unchanged kernel (public API only).
use std::time::Instant;
use tatic::kernel::*;

mod driver;
mod encoding;
mod wasm;
mod lemma_cache;
mod rewrite;
mod machine;
mod miner;
mod search;
mod task;
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

// The allocator `main.rs` ships with: the lib's own `#[global_allocator]` is
// `#[cfg(test)]`, so without this these timings ran on the system heap.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
