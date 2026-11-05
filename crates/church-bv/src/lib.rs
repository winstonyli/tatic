// A fixed-width bit-vector as a Church-encoded n-ary tuple of Church Bools, with an
// unrolled ripple-carry `add`, on the unchanged kernel (public API only).

// Until the bin exists (step 2) only the tests use this code, so a non-test build sees it as unused; step 2 deletes this line.
#![cfg_attr(not(test), allow(dead_code, unused_imports))]

use std::time::Instant;
use tatic_kernel::*;
use std::sync::Arc;
use job::{Job, Setup};

mod belief;
mod classes;
mod ctx_scorer;
mod corpus;
mod driver;
mod encoding;
mod job;
mod wasm;
mod lemma_cache;
mod rewrite;
mod machine;
mod miner;
mod search;
mod task;
mod uniform;
mod work;
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

// The unit-test exe's allocator, so its timings run on what ships; a binary on this lib (step 2) carries its own.
#[cfg(test)]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
