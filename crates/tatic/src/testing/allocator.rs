//! The allocator `src/bin/demo.rs` ships with, so timing probes in the lib's tests measure what runs (docs/related-work/ §66). This
//! covers only the lib's own unit tests: an integration test (`tests/*.rs`) or bench is its own binary and needs its own
//! `#[global_allocator]` to time anything, else it runs on the system heap (about 2x slower on the lemma in `church-bv`).
//! Declared in `src/bin/demo.rs`, `benches/*.rs` and `crates/church-bv/src/lib.rs`; add it to any new timing test.

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
