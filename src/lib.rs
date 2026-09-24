pub mod compile;
pub(crate) mod decompile;
pub mod eval;
pub(crate) mod ir;
pub mod jit;
pub mod kernel;
pub(crate) mod lower_wat;
pub mod proof;
pub mod spec_check;
pub mod specialise;
pub mod syntax;
pub mod term;
pub mod typing;

// Lets `test_corpus` include `benches/common.rs`, which names the crate
// `tatic` as the benches do.
#[cfg(test)]
extern crate self as tatic;
#[cfg(test)]
pub(crate) mod test_corpus;
#[cfg(test)]
mod ir_fuzz;
#[cfg(test)]
mod independence;
