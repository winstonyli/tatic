---
status: done
---

# Trusted lemma cache across a loop's processes (plan, approved direction: trusted, audit switch, loop-scoped)

**Status: implemented 2026-10-12** (all steps; results in docs/tier-cycle.md, "A trusted lemma cache per loop").

**Goal:** a closed lemma (`shared_lemma`: rule lemmas, the machine proofs' case lemmas, `good_*`, `assoc`, `comm`) is built and
checked once per loop, not once per process. Today the mine and every serving process build and check the lemmas they use
from scratch (`CLOSED` is per thread and per process).

**Expected gain** (docs/tier-cycle.md, "Serving's lemma cost is checking, not building" and "Which lemmas repeat"): in the
cmp3d ref loop (`RULEMINER_FAST=1`), lemmas are 95% of serving and their kernel checks 73-77% of that; of serving's 29.5 s of
lemma time, 20.6 s is lemmas an earlier process of the loop already built. A trusting cache saves about 28 s of the 68 s loop.
In a sweep this applies to the `mines` stage (ref loops, serving with proofs) and to every loop's mines (winners are proved);
the `own`/`pooled` loops serve with `CHECK_FAST=1` and build no lemmas.

## Design

A lemma is used only as a parameter: `shared_lemma` checks the proof (`ck`), then binds the statement as a `Free`
(`Postulates::bind`), and every later use is checked against that parameter, never against the proof (`discharge`, which
puts the proofs back, is used by one test only). So **the cache stores statements, not proofs**: on a hit the statement is
bound without building or checking a proof.

- **Soundness rests on one thing:** every statement in the file was checked (`ck`) by a process of this same build. A key
  that is wrong or incomplete cannot make a false statement usable: the entry's statement was still proved, and a use that
  expects a different statement fails the kernel check (as a wrong in-process `CLOSED` hit would today). So string keys need
  not be injective for soundness; key completeness is a matter of not failing, which the audit checks.
- **Scope:** one file per loop, `LOOP_OUT/lemmas.bin`. The driver deletes it when a loop starts and when it ends (a sweep
  has dozens of loops and the disk is 94% full) and passes `LEMMA_CACHE=<path>` to the loop's children (mines and serving).
  Children of a loop run one after another (`driver::child` waits), so there is one writer at a time; parallel sweeps use
  different `LOOP_OUT`s.
- **Build identity:** the file header is `magic, exe hash` (a hash of the bytes of `current_exe()`, computed once per
  process; any change to the format changes the exe, so no separate version). A file from another build, or a truncated or
  corrupt file, is ignored as a whole (all misses, rebuilt and overwritten at save) with one stderr line saying why.
- **Audit switch:** `LEMMA_RECHECK=1` builds and checks every lemma as today and, for each one the file has, asserts that the
  built statement equals the stored one (structural `==`), panicking with the key otherwise. Used once per change to the
  lemma code, not in timing runs.
- **Statements only, closed only:** a statement with a `Free`, `Const` or loose `Var` (`free_of`, `loose_of`; none of
  today's do) is not recorded, and counted (`skipped` in the stderr line), so a later lemma kind that needs parameters in its
  statement stays correct, just uncached.
- **Recording:** each statement a process checks is encoded right after its `ck` (`Expr` is `Rc`, not `Send`) and pushed to a
  process-wide `Mutex<Vec<(String, Vec<u8>)>>`, so lemmas built on miner worker threads are kept too (the old draft's
  main-thread-only restriction goes).
- **Loading:** lazily, at the first `shared_lemma` miss in `CLOSED` of the process: read the file once into a process-wide
  `OnceLock<Option<Loaded>>` of key -> encoded bytes. A hit decodes the statement in the calling thread (through the public
  constructors, so it is interned in the current scope), binds it, and memoises it in `CLOSED` as a built lemma would be. A
  process that builds no lemma (serving with `CHECK_FAST=1`) never reads the file.
- **Saving:** a guard (`lemma_cache::Save`) at the top of `rule_miner` and `rule_set_kernel_check` writes on drop (every
  return; also on unwind, which is still sound since every recorded statement was checked): the loaded entries' bytes, then
  this process's new ones not already loaded (first one wins per key), to `lemmas.bin.tmp`, renamed over `lemmas.bin`. Nothing
  is written when nothing was recorded. Saving never panics (an error is one stderr line), since it may run during an
  unwind. Prints `LEMMA_CACHE loaded=<n> hits=<h> built=<b> saved=<s> skipped=<k> bytes=<B>`.
- **`discharge`:** `PARAMS` keeps `Option<Expr>` proofs; `discharge` panics on a loaded lemma (`None`) naming
  `LEMMA_CACHE`. Its one test runs without `LEMMA_CACHE`.
- **Keys:** the existing strings (`rule_..`, `tree|..`, `good_add..`, `assoc..`, `comm..`). The typed `LemmaKey` and binary
  `Term` key of the old draft are parked: they add size, not soundness (see above), and the audit is what catches an
  incomplete key.

## Pieces

1. **`src/kernel/bin.rs`**, `pub mod bin` under `kernel`: the binary `Expr` format (the compressed counterpart of the text
   format the user plans). A node table in post-order, each distinct node (by `Rc` pointer; in an `InternScope` equal
   subterms share one) once: a tag byte per variant, then LEB128 varints (the `u32` of `Var`/`Sort`, child node indices).
   - `pub fn write(e: &Expr) -> Result<Vec<u8>, String>`: `Err` on a `Const` or `Free` (statements are closed).
   - `pub fn read(b: &[u8]) -> Result<Expr, String>`: through `var`, `sort`, `pi`, `lam`, `app`, `id`, `refl`, `jelim`,
     `wty`, `sup`, `wrec`, `sigma`, `pair`, `sigrec`; `Err` on a bad tag, an index out of range, trailing or missing bytes.
   - The match in `write` is exhaustive over `Expr`, so a new variant fails to compile until the format covers it.
2. **`tests/church_bv/lemma_cache.rs`** (registered in `main.rs`):
   - `struct Cache { path, entries: HashMap<String, Vec<u8>>, order: Vec<String>, why_empty: Option<String> }` with
     `Cache::load(path, identity: u64) -> Cache`, `get(&key) -> Option<&[u8]>`, and
     `save(&self, new: &[(String, Vec<u8>)], identity) -> io::Result<usize>`.
     File: `b"TLC1"`, `u64` identity (little-endian), then entries `varint key_len, key, varint stmt_len, stmt`.
   - The process-wide layer: `exe_identity()`, `recorded: Mutex<Vec<..>>`, counters, `lookup(key) -> Option<Expr>`,
     `record(key, &stmt)`, `struct Save` (drop = save, print the line).
3. **`shared_lemma`** (rewrite.rs): on a `CLOSED` miss, `lookup(key)`: a hit binds the decoded statement with no build or
   `ck` (with `LEMMA_RECHECK=1`: build, `ck`, assert equal, then bind the built one); a miss builds, checks, records, binds.
4. **Driver:** `run_loop` removes `out/lemmas.bin` at start and adds `LEMMA_CACHE` to `common`; the module doc lists it.

## Stress test

Round 1 (soundness and scope):
- A loaded statement is trusted only as a parameter type; `bind` still type-checks it as a type (`infer_open`), so a
  decoded term that is not a type panics there rather than entering the context. Cost: one `infer_open` per hit (small next
  to `ck`; measured in step 4's counters if it shows).
- A stale file from an older build of the same loop dir: the identity check drops it, and the driver deletes it anyway.
- Rows must not depend on the cache. M and the rules come from the rewriter's decisions, which read plain Booleans, not
  kernel terms (2bf9c7a), and a cache hit only skips building a proof the writer already built successfully. The pair sweep
  checks it (identical rows, preferences and rule/unit files).

Round 2 (process and thread facts, checked in the code):
- `driver::child` runs `current_exe()` (same exe, same identity) and waits (`status()`); loops of a sweep run one after
  another.
- `CLOSED` and `PARAMS` are thread-local; the recorder and the loaded map are process-wide and hold bytes only, so worker
  threads' lemmas are recorded and every thread can hit.
- `rule_set_kernel_check` returns early under `CHECK_FAST` (after the `CHECKED` line) and `rule_miner` may return early;
  the drop guard covers both. On a panic the guard still saves only checked statements.
- Statements in use are closed: tree lemmas are `lemma_n_ty` (closed by construction), rule lemmas `prove_rule`'s
  `Pi`-over-`Bv` statements, `good_*`/`assoc`/`comm` closed; the recorder's closedness check enforces it rather than trusting
  this list.

Round 3 (keys, audit, measurement):
- Tree keys include the machine, `k`, `nv`, the tag (which carries `enc.g[j]` or `dec`), the invariant and `enc.phi[side]`;
  rule keys `rule_<name>_<l>_<r>_<n>` lack `k` (the round 3 finding of the old draft: `prove_rule(n, k, ..)` with
  `k = args.len()`). Today `k` equals the rule's variable count, so the audit run will pass; add `k` to the key anyway (one
  `format!` change) so a cached rule lemma cannot be bound under a statement of another arity.
- The audit run (`LEMMA_RECHECK=1`) must use a loop where every lemma kind hits: the cmp3d ref loop (machine proofs, rule
  lemmas, `good_*`), salt 1.
- Timing: same-load pair sweep against the commit before, salts 1 and 2, `SWEEP="mines own pooled"`; the gain should show
  in the `mines` stage and the loops' mines.

Round 4 (does skipping `build` change anything but time?):
- No decision reads a lemma build. `MACHINE_FALLBACKS` (the CHECKED line, M) is counted in `machine_fallback`, on the
  decision path, from `tree_encoding`, not from `tree_proof`. The miner's `prove_rule(..).is_some()` (its filter under
  `RULEMINER_FAST`) comes from the encoding search and the final `holds`; a lemma build inside it either succeeds or panics
  in `ck`, never returns a soft failure, so a hit cannot flip it. Build closures' other side effects: `GUARDTRACE` prints
  and the `DD_LEMMAS` thread-local (a cache).
- Deleting the file at loop end and the never-panicking save were added here; the format version was dropped (the exe hash
  covers it).

Round 5 (found nothing material): `PARAMS` grows over a process as today, loaded lemmas included; `holds` checks a proof
that uses a loaded lemma against its parameter, as for a built one; the sweep's `loop` loops get hits in their second and
third mines (serving there is `CHECK_FAST` and reads nothing).

## Steps

1. `bin.rs` + test `bin_round_trips_a_case_lemma_statement` (a `lemma_n` statement over 3 bits and one built in an
   `InternScope`: `read(write(e)) == e`, and the node table has as many entries as distinct pointers) and
   `bin_rejects_bad_input` (truncated, bad tag, out-of-range child, `Free` on write).
2. `lemma_cache.rs` + test `lemma_cache_round_trips_and_rejects_other_builds` (save then load: entries back, statements
   equal; another identity, another magic, a truncated file: empty with a reason).
3. Wire `shared_lemma`, `discharge`, the guards, the driver, the rule key's `k`. All church_bv tests pass.
4. Audit: the cmp3d ref loop with `LEMMA_RECHECK=1` (`RULEMINER_FAST=1`, salt 1): no mismatch; the `LEMMA_CACHE` lines show
   hits in every serving process.
5. Pair sweep; record in docs/tier-cycle.md and docs/runs/2026-10-12 (rows, script, README row); commit.
