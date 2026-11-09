//! A minimal predicative dependent type theory kernel: Pure-Type-System-style
//! Pi + a stratified universe hierarchy, plus Id-types, W-types, and
//! Sigma-types as the additions beyond a bare PTS.
//!
//! Five primitive term/type formers, total:
//!   - `Sort(i)`: the universe hierarchy `Type_0 : Type_1 : Type_2 ...`
//!   - `Pi`/`Lam`/`App`: dependent function types
//!   - `Id`/`Refl`/`J`: propositional equality, with its eliminator
//!   - `W`/`Sup`/`WRec`: well-founded trees, i.e. *the* generic strictly
//!     positive inductive type former (Bool, Nat, lists, and eventually
//!     this crate's own `Term` AST are all instances of one `W`, not
//!     separate primitives)
//!   - `Sigma`/`Pair`/`SigRec`: dependent pairs. *Not* derivable from the
//!     other four here: `W`'s own children function maps back into `W`
//!     itself (`B(a) -> W(A,B)`), so it can only stand in for a payload
//!     that's *another instance of the same inductive type* -- it can't
//!     express an arbitrary, independently-chosen payload type `B(a)`
//!     the way a general dependent sum needs. The usual alternative,
//!     Church/impredicative-encoding `Sigma` from `Pi` alone, was rejected
//!     for the same reason Church-encoding inductive types was rejected in
//!     favor of `W`: it doesn't reduce by `refl`, only propositionally.
//!
//! Everything else (Bool, Nat, non-dependent pairs, ...) is a *definition*
//! built from these five, not a further primitive. See the tests in `tests/` (`crates/tatic-kernel/src/tests/`)
//! for worked examples, including a proof that uses `J` (symmetry
//! of `Id`), a `WRec`-defined function whose defining equation holds by
//! `refl` alone (i.e. genuinely *computes*, which is the whole point of
//! choosing `W` over an impredicative/Church encoding), and a `SigRec`
//! projection that computes the same way.
//!
//! Besides those formers a term has `Var` (de Bruijn index), `Free` (a level, for builder parameters) and `Const`
//! (a postulate or definition in `Globals`).
//!
//! This is the trusted core: the proof pipeline (`proof`, `jit`) builds terms and has this module check them; nothing
//! else decides equality or typing. Layout: this file declares the pieces and re-exports them; `expr` holds `Node`/`Expr`
//! and the builders, `stack` the stack growth every traversal shares, `show` the printers, `subst` `shift`/`instantiate`,
//! `hc` the hash-consed memos, `reduce` `whnf`/`def_eq`/`normalize`, and `check` `infer`/`check` with their context and memo.
//! Child modules: `postulates` (builders over `Globals`, not read by the checker) and `tests`.

use hashbrown::HashMap;
use std::fmt;
use spaces::{IdMap, IdSet, Ref, Spaces};

mod spaces;
mod postulates;
mod expr;
mod stack;
mod show;
mod hc;
mod subst;
mod check;
mod reduce;

pub use expr::*;
pub use stack::*;
use show::*;
pub use subst::*;
pub use check::*;
pub use reduce::*;
pub use postulates::*;

pub mod bin;

#[cfg(test)]
mod tests;

// The allocator the lib's tests are timed under (`tatic/src/lib.rs`): the wall-clock ratio tests (`assert_scales` in `tests.rs`, its callers in `tests/`)
// measure against it. The integration tests in the crate's `tests/` directory (outside `src/`) time nothing, so they stay on the system heap.
#[cfg(test)]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
