---
status: active
---

# Split `encoding.rs` by concern (TB3, `encoding` half)

Parked item "Split `encoding.rs`" in `PARKED.md`; the method is the one of `docs/superpowers/specs/2026-11-04-rewrite-split-design.md`
(done). Facts below are from a read-only look on 2026-11-04 (commit 291cb59); line numbers drift, the plan's first task re-derives them.

## Intent

`crates/church-bv/src/encoding.rs` is 1979 lines: Church Bool and vector builders, the "good" (well-formedness) witnesses, the
division and equality lemmas, the add proofs, the truth-table builders, and 26 tests (7 `#[ignore]`d) interleaved with the items
they test. After the split each concern is a file under `encoding/`, the tests are one file, and nothing else changes.

## Decided by the user (2026-11-04)

- c1 then e1: the boundaries below were proposed and approved ("e1"); this spec records them. Same mechanism as `rewrite/`: the
  parent `encoding.rs` re-exports every piece with `pub use piece::*`, so `lib.rs`'s `use encoding::*` and every caller stay as they
  are; all tests move to `encoding/tests.rs`.

## Design

| New file | Concern | Items (by name; the plan derives ranges) |
|---|---|---|
| `encoding/gates.rs` | memo and gate builders | `Fx`, `GenMemo`, `gen_memo`, `constant`, `bool0`/`t`/`f`/`bit`/`bool2`, `and_`/`or_`/`xor_` and `and`/`or`/`xor`, `low_bits`, `karrow`, `bv_ty`, `apps`, `binders`, `bits_to_bv`, `lit`, `add`/`sub`/`lt_u`, `ripple_carry`, `ripple`, `add_shared`, `is_ok` |
| `encoding/good.rs` | the "good" witnesses and their lemmas | `good_bool`, `bit_lemma`, `church_tuple`, `good_bv_step`, `good_bv`, `holds`/`ck`/`checked`, `good_bit`, `lemma2`, `id_t`, `hyp_or_refl`, `and_peel`, `good_and_lemma`, `bit_from_xnor`, `good_xnor_lit`, `bit_lemma_hyp`, `good2`, `good_add`/`good_sub`/`good_ripple`/`good_vec`/`good_lt`, `good_bool0`, `good0_bit`, `lower_bit`, `good_bv0*`, `lower_bv*` |
| `encoding/division.rs` | equality, wrapping division, `Nat` lift | `not_`, `mux`, `eq_bv`, `wrap_div`, `wrap_div_min_proof`, `nat_ty`/`nat_lit`/`nat_add`, `good_bv1`, `lift_good`, `to_n`, `good_lit`, `sdiv_some`, `eq_lit_sound`, `min_all`, `sdiv_none_*`, `wrap_div_keeps_r` |
| `encoding/proofs.rs` | the add identity / commutativity / associativity / `add_not` / `or_disjoint` proofs | `add_zero_proof`, `add_identity_proof*`, `comm_lemma`, `add_comm_proof`, `add_assoc_proof`, `add_not_proof`, `or_disjoint_proof`, `bitwise`, `or_bv`, `good_or_bv`, `good_tuple` |
| `encoding/tables.rs` | truth-table and BDD builders, the assoc tables | `TabBdd`, `tab_bdd`, `table_app`, `table_expr`, `lemma_n`, `lemma_n_ty`, `sum3`, `maj`, `assoc_table`/`assoc_side`/`assoc_g`, `Gb`, `GoodOps` |
| `encoding/tests.rs` | every `#[test]`, scaling probe and test-only helper | scattered |
| `encoding.rs` | `mod` lines, `pub use piece::*`, shared `use` lines | about 20 |

The table is the user-approved boundary; where an item's real callers say another piece owns it, the plan's rule decides (with its
only caller; else with the concern that owns its data) and the ruling goes in the ledger. A `pub fn` that only tests call stays in
the piece of its concern (not in `tests.rs`) unless it is `#[cfg(test)]` or a `#[test]`.

**Mechanism** as in the `rewrite` spec: each piece starts with `use super::*;`; whatever was private and is used from another
piece gets `pub(super)` on its own line (the compiler lists it); a `pub fn` that mentions a type that is only `pub(super)` becomes
`pub(super)`, never widen a type. No cycle-breaking edit is expected; if `proofs` and `good` call each other that needs only
visibility.

**Hidden state.** `job.rs`'s `hidden_state_is_classified` lists `("encoding.rs", "CONSTANTS")` and `("encoding.rs", "BODIES")`.
They become `("encoding/gates.rs", "CONSTANTS")` and `("encoding/tables.rs", "BODIES")` (or the file the plan finds them in). Its
directory walk reads `src/` and `src/rewrite/` today; it generalizes to the pieces' directories (`src/rewrite/`, `src/encoding/`),
with `/` as the separator. `src/uniform/` is not in the walk today; adding it is not part of this change.

**Test names.** The 26 tests become `encoding::tests::<name>`; the baseline is compared after mapping that segment back; scripts
and docs that name an ignored `encoding::<test>` by path are repointed (the plan greps for them).

**Docs.** The 3 `encoding.rs#symbol` cites in `docs/TOUR.md`, the `PARKED.md` mentions that name a symbol, and the module line in
`TOUR.md` (gains the piece list). `docs/tier-cycle.md`, `RELATED_WORK.md`, `docs/runs/` and dated plans are history and are left.
`tour_check` and `cite_check` pass. The `PARKED.md` entry for this split is deleted.

## Non-goals

Behaviour, item names, signatures, test bodies, or proof content; `pub` trimming; making anything wider than `pub(super)`.

## Anti-goals

An item whose body differs by a byte beyond a `pub(super)` keyword; a `thread_local!` cut from its accessor or in two; a test that
stops running; a hidden-state entry that silently stops matching (Task 3 breaks one on purpose and expects FAIL).

## Verification

Sorted multiset of trimmed non-blank lines of the old file equals that of the new files plus the parent, modulo `pub(super) `, `mod`,
`pub use` and `use super::*;` lines; test list equal to the baseline modulo `tests::`; `cargo check --workspace --all-targets`; the
lib suite; the full suite through `run.ps1`; `test_gate.sh`; one reference sweep identical (`WORK`, result files, `cold_streams.tsv`
minus its seconds column); `tour_check`, `cite_check`. Instruction counts are not needed: the sweep's `WORK` lines and result files
already show the same work (the `rewrite` split's count was equal within 0.5%).

## Left to the builder

Which side of a boundary a small helper lands on; the exact `pub(super)` list.
