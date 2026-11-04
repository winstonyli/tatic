pub mod jit;
pub mod kernel;
pub mod lang;
pub mod proof;
pub mod support;
pub mod verify;

// The allocator `src/bin/demo.rs` ships with, so timing probes in the lib's tests
// measure what runs (RELATED_WORK §66). This
// covers only the lib's own unit tests: an integration test (`tests/*.rs`) or
// bench is its own binary and needs its own `#[global_allocator]` to time
// anything, else it runs on the system heap (about 2x slower on the lemma in
// `tests/church_bv.rs`). Declared in `src/bin/demo.rs`, `benches/*.rs`
// and `tests/church_bv/main.rs`; add it to any new timing test.
#[cfg(test)]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
#[cfg(test)]
mod testing;
