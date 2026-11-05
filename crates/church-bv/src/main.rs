//! `church-bv <subcommand>`: the entry points of the research drivers (see `church_bv::entry`).

// The lib's allocator is `cfg(test)` only; the binary carries the one that ships.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> std::process::ExitCode {
    church_bv::entry::main()
}
