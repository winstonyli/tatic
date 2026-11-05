//! Test-only support (compiled under `cfg(test)`).

mod allocator;
pub(crate) mod independence;
mod ir_fuzz;
pub(crate) mod test_corpus;
