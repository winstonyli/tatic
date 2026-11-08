//! Church encodings of fixed-width words and a wasm machine over them, on the unchanged kernel (public API only):
//! `encoding` holds the words, gates and their proofs, `wasm` the instruction set and its meaning. church-bv (the miner)
//! and tatic (the JIT) both build on it.

use std::time::Instant;
use tatic_kernel::*;

pub mod encoding;
pub mod wasm;

use encoding::*;

// The unit-test exe's allocator, so its timings run on what ships.
#[cfg(test)]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
