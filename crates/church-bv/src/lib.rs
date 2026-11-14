// A fixed-width bit-vector as a Church-encoded n-ary tuple of Church Bools, with an
// unrolled ripple-carry `add`, on the unchanged kernel (public API only).

// An item only the tests reach is `#[cfg(test)]`, so both builds are free of dead code and unused imports, and stay so.
#![deny(dead_code, unused_imports)]

use std::time::Instant;
use tatic_kernel::*;
use std::sync::Arc;
use job::{Job, Setup};

mod classes;
#[cfg(test)]
mod corpus;
mod driver;
#[cfg(test)]
mod encoding_scaling;
pub mod entry;
mod host;
mod job;
mod lemma_cache;
mod rewrite;
mod machine;
mod miner;
mod search;
mod streams;
mod task;
mod work;
#[allow(unused_imports)]
use tatic_wasm::encoding::*;
#[allow(unused_imports)]
use rewrite::*;
use host::*;
#[allow(unused_imports)]
use machine::*;
#[allow(unused_imports)]
use search::*;
#[allow(unused_imports)]
use streams::*;

type BitTriple = (Vec<Expr>, Vec<Expr>, Vec<Expr>);
/// Output bits of a circuit from the two operands' bits.
#[cfg(test)]
type BitsDyn = dyn Fn(&[Expr], &[Expr]) -> Vec<Expr>;

// The unit-test exe's allocator, so its timings run on what ships; the binary (`main.rs`) carries its own.
#[cfg(test)]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
