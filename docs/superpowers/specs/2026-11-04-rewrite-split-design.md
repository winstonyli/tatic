---
status: done
---

# Split `rewrite.rs` by concern (TB3, `rewrite` half)

Item TB3 of `docs/superpowers/plans/2026-11-04-cleanup-restructure.md`. Facts below are from a read-only survey on 2026-11-04
(commit e7c8427; line numbers drift, the plan's first task re-derives them).

## Intent

`crates/church-bv/src/rewrite.rs` is 4475 lines and holds seven concerns plus 51 interleaved tests (about 1,100 lines;
the last ~1,060 lines are nearly all tests under a stale header comment, "Searching for the carry-state encoding"). After the
split the concerns are separate files under `rewrite/`, the tests are one file, and nothing else in the crate changes.

## Decided by the user (2026-11-04, "as rec")

- c1: `rewrite.rs` only. `encoding.rs` (1979 lines, five concerns) is a follow-up: parked in `PARKED.md` with this spec as its
  model.
- d1: `rewrite.rs` stays as the parent module and re-exports its pieces (`pub use piece::*`); `lib.rs`'s `use rewrite::*` and
  every caller stay as they are.
- e1: all tests move to `rewrite/tests.rs` (the SR5 convention, `foo/tests.rs`).

## Design

**Files** (regions from the survey; ranges are approximate and are re-derived by the plan's Task 1):

| New file | Concern | Lines (of the old file) |
|---|---|---|
| `rewrite/term.rs` | interner, `Term`, operator constants and `OpInfo`, `impl Term` | 1-523 |
| `rewrite/values.rs` | `Word`, `ValueMemo`, the screens, generic law builders (`bitwise_law`, `k_var_law`, ...) | 524-916 |
| `rewrite/plan.rs` | lemma memo (`CLOSED`, `memo`, `shared_lemma`, `discharge`, `witnessed`), `Plan`, `LawKind`, `Compiler` | 917-1148 |
| `rewrite/rules.rs` | `Rule`/`Rules`, `RuleTable`, `PatIndex`, fixed and promoted rules, rule order, matching, unification, `rule_step`, rule proving | 1149-1974 |
| `rewrite/rewriter.rs` | `Trace`, `RewriteMemo`, `RewriteState`, `rewrite`, `rewrite_memo`, `rewrite_uncached` | 1975-2450 |
| `rewrite/join.rs` | `JoinCost`, `JoinStore`, `prove_eq`, `join_eq`, `join_walk`, `join_search` | 2451-3297 |
| `rewrite/laws.rs` | `shr_mask_eq`, `rewrite_plan`, `rewrite_law`, `law_proof`, the carry-chain builder | 3298-3401, 3610-3702 |
| `rewrite/tests.rs` | every `#[test]` and test helper (`join_trace`, `PIN_SOURCE`, ...) | scattered |
| `rewrite.rs` | `mod` lines, `pub use piece::*`, the shared `use` lines | about 30 |

**Mechanism.** Each piece starts with `use super::*;` and sees every sibling through the parent's glob re-exports (a glob
import brings in the parent's private `use` imports and the crate root's names as today). The parent keeps the old file's `use super::*;` and adds one explicit `pub use term::Node;`: the crate root globs both `tatic_kernel::*` (a generic `Node`) and `rewrite::*`, today the local definition shadows the kernel's, and after the split the parent would hold two competing globs (E0659 in every piece but `term`); an explicit import wins. Whatever was private and is used from another piece (an item, a struct field, a method; the survey found `Rules.table`, `RuleTable.join*`, `Trace.items`, `RewriteMemo.joins`, `ValueMemo.vars`, `JoinEq.need`, `Term::sh` and others) gets a `pub(super)` visibility keyword on its own line (the compiler lists them); a `pub` item stays `pub`. A `pub` signature that mentions a type now only `pub(super)` would raise `private_interfaces`: make that function `pub(super)` too, never widen a type. The call cycle
`rewrite_uncached` -> `prove_eq` -> `prove_rule` -> `rewrite_uncached` crosses `rewriter`, `join` and `rules` and needs no
change beyond visibility. `tests.rs` has `use super::*;` and so reaches the `pub(super)` items.

**Hidden state.** `job.rs`'s `hidden_state_is_classified` lists statics by file name: `("rewrite.rs", "OP_CACHE" | "CLOSED" |
"COUNTING" | "TABLE" | "CACHE")` become `("rewrite/term.rs", ...)` and so on (its scan, `read_dir(src)`, skips directories today, so `src/uniform/` is not scanned; Task 3 makes it also read `src/rewrite/*.rs`, keyed as `rewrite/<file>`, with `/` as the separator on every platform).

**Test names.** The 51 tests become `rewrite::tests::<name>`; the baseline list is compared after mapping that prefix back. No
test is renamed, deleted or edited.

**Docs.** About 25 `path#symbol` cites in `docs/TOUR.md` (rewrite.rs), the `PARKED.md` mentions that name symbols, and the code
comments naming the file are repointed to the new file by symbol; bare `rewrite.rs` stays where the parent is meant.
`docs/tier-cycle.md`, `RELATED_WORK.md` and `docs/runs/` are history and are left. `TOUR.md` gains the piece list; `tour_check.sh`
and `cite_check.sh` pass.

## Non-goals

Any change to behaviour, names of items, signatures, test bodies or the order of rules; splitting `encoding.rs`; making
anything `pub` that was private beyond `pub(super)`; trimming the 35 `pub` names no other file uses (that is a separate
visibility pass).

## Anti-goals

A moved item whose body differs from the old one by a byte beyond indentation; a thread-local or static that changes thread
or lifetime semantics (a `thread_local!` stays in one `thread_local!` block with its fn); a test that stops running; a
hidden-state entry that silently stops matching (the test must still FAIL on an unclassified static: Task 3 checks this by
temporarily renaming one entry).

## Verification

Item bodies identical (the plan's Task 2 diffs the sorted multiset of non-blank, trimmed lines of the old file against the new
files plus the parent: only added lines are `mod`, `pub use`, `use super::*;`, `pub(super)`/visibility edits and file headers);
test list equal to the baseline modulo the `tests::` segment; `cargo check --workspace --all-targets` clean apart from the 2
known warnings; the lib suite; `test_gate.sh`; one reference sweep identical (`WORK`, result files); instruction counts of the
bin on that sweep equal to before within the spread (a pure move should be equal to a few ppm: the same code, only symbol
order differs); `tour_check`, `cite_check`.

## Left to the builder

Exact piece boundaries where the survey's ranges fall inside an item; which side of a boundary a small helper lands on (the
rule: with its only caller, else with the concern that owns its data); the names of nothing else.
