//! Test-only support (compiled under `cfg(test)`).

mod allocator;
pub(crate) mod independence;
pub(crate) mod ins_mutate;
mod ir_fuzz;
pub(crate) mod test_corpus;
