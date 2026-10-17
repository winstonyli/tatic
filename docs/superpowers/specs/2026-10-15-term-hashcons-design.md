---
status: done
---

# Hash-consed `Term` for church_bv's miner: spec (draft 3, 2026-10-15)

Status: design approved section by section (2026-10-15); built in 32510ae and adopted in d61d381. The decision and its
measurements are in `docs/tier-cycle.md` ("Where a sweep spends its time").
(V) = read in the code or measured; (U) = unverified.

## Goal
Make `rewrite::Term` clone, drop, hash and equality O(1) by hash-consing it, so a full sweep stops paying for boxed
trees. A samply profile of a salt-1 sweep on 744b31d (tier-cycle.md, "Where a sweep spends its time") charged
`Term` clone 13.3%, SipHash on `Term`s 11.9%, `Term` drop 6.9% and mimalloc 20.6% (inclusive, overlapping); the
kernel is 10.9%.

Success criteria (chosen 2026-10-15):
1. A fixed-salt sweep's outputs are identical apart from seconds (rule below).
2. The church_bv tests pass.
3. Twelve alternating full sweeps show the CPU change.

Non-goals: `Term` by value in signatures, a cheaper hasher for `Term`-keyed maps, memoized `show_cmp`, rebasing
`SigMemo` on node ids, freeing nodes. Each is listed under "Follow-ups".

## What exists (V)
- `tests/church_bv/rewrite.rs:5-11`: `#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)] pub enum Term { V(usize),
  Zero, Ones, Op(usize, Box<Term>, Box<Term>) }`, 32 B. No `Debug`. Nothing mutates a `Term` in place (no
  `&mut Term`).
- Only church_bv uses it (rewrite.rs, search.rs, machine.rs). Lines matched (grep -c): 89 with `Box::new` (rewrite 35, search 28,
  machine 26; 83 of them `Term::Op(...Box::new`), 158 with `Term::Op`, 81 with `Term::V(`, 130 with `Term::Zero`/`Term::Ones`,
  21 `matches!` and 12 `if let` on `Term::`.
  Variable indices go past 8 when rules are renamed apart (`Term::V(i + k)`, rewrite.rs:899 and 1288; `V(4 + j)`,
  search.rs:658).
- Ordering: the derived `Ord` makes canonical keys only (doc comment at rewrite.rs:4; the key sort at search.rs:864
  for the `picks`/`finished` maps). Output orders use `show()` text (`show_cmp`).
- Hashing: every `Term`-keyed map uses std `RandomState`. The only fixed-seed hashers are encoding.rs's `Fx`
  `GenMemo`s (keyed by `usize` and `Vec<bool>`) and lemma_cache.rs's `DefaultHasher` over the exe bytes.
- Threads: miners score on `RULEMINER_THREADS` scoped workers (default 1, clamped to 1..=12, search.rs:429); the
  driver's pool is `THREADS` (default 2). Statics holding `Term`s: `OnceLock`s (`rule_set`, `promoted_rules`), the
  `pool3_sequence` `MEMO` Mutex (search.rs:233, shared across threads), and thread-locals (`EXTRA_RULES`, `RULE_TRACE`, `REWRITE_PATH`, `TREE_LAWS`, `TREE_ENCS`).
- Terms leave the process only as text (`show`, `parse_term`); the kernel bridge is `Term` to `Expr` (`eval`).
- Distinct nodes, measured (2026-10-15, probe reverted): a fingerprint of every `Op` node at drop, over a salt-1
  sweep. At most 57,272 distinct per process (the driver; 32,086 in the largest miner, `lib_cmp3d`, against
  64.8 M node drops), 1.26 M summed over the sweep's 171 processes.

## Design

### Representation (rewrite.rs)
```rust
#[derive(Clone, Copy)]
pub struct Term(&'static Node);
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Node { V(usize), Zero, Ones, Op(usize, Term, Term) }
```
- Leaves are statics, never in the table: `static LEAVES: [Node; 64]` (`Node::V(i)` at `i`), `static ZERO_NODE`,
  `static ONES_NODE`; `pub const ZERO: Term = Term(&ZERO_NODE)` and `ONES` likewise (a `const` naming a `static`
  needs Rust 1.83; the toolchain is newer, (V) `rustc --version`); `Term::v(i)` returns
  `Term(&LEAVES[i])` and asserts `i < 64`. The consts must point at `static`s, not at promoted constants
  (`&Node::Zero`), since a promoted constant's address is not guaranteed unique.
- `Term::op(o, a, b)` interns: it returns the one node equal to `Node::Op(o, a, b)`, leaking it on first sight.
- `t.node() -> &'static Node`; sites match `*t.node()`, whose bindings are by value.
- `PartialEq`/`Eq`: `std::ptr::eq`. `Hash`: the address. Sound because every `Op` is interned and every leaf has one
  static, so equal structure means equal address. `Node`'s derived `Eq` (the table's equality check) is then O(1)
  too, since its fields are `usize` and `Term`; `Node` needs no `Hash` (the table hashes by hand, below).
- `Ord`/`PartialOrd`: hand-written, equal to the old derived order: `V < Zero < Ones < Op`; `V` by index; `Op` by
  operator, then left, then right. Pointer-equal terms return `Equal` first. Structural (not address) order keeps
  every sort's result identical to today's.
- `show`, `show_cmp`, `size`, `eval`, `occurrences` and the rest keep their logic; only the match syntax changes.

### Use sites (rewrite.rs, search.rs, machine.rs)
- `Term::Op(o, Box::new(a), Box::new(b))` becomes `Term::op(o, a, b)` (`op` takes `Term`s by value, so a `&Term`
  argument is passed as `*a`); `Term::V(i)` construction becomes
  `Term::v(i)`; `Term::Zero`/`Term::Ones` become `Term::ZERO`/`Term::ONES` (also the `&Term::Zero` temporaries, now
  `&Term::ZERO`).
- Patterns: `match t { Term::Op(o, a, b) => … }` becomes `match *t.node() { Node::Op(o, a, b) => … }`; tuple matches
  (unify) match `(*ra.node(), *rb.node())`; `matches!` and `if let` likewise. Bindings are values, so `*o`, `*i`
  derefs go.
- Every `.clone()` of a `Term` is removed (clippy's `clone_on_copy` finds the rest).
- Signatures keep `&Term` (decided 2026-10-15: by value adds a few hundred call-site edits for no measured gain).
- Collections, statics, the text round trip and the `Expr` bridge are unchanged apart from match syntax.
- One commit: the type change breaks every site at once.

### Threads and memory
- The table: `static SHARDS: [Mutex<hashbrown::HashTable<&'static Node>>; 16]` (hashbrown 0.16 is a dependency;
  `HashTable` takes the hash from the caller). The hash is a small hand-written mix of the operator and the two
  child addresses, with no seed: the table hash is the whole value and the shard is bits 40..44, which hashbrown uses for neither its
  tag (top 7 bits) nor its bucket index (low bits, below 2^17 entries). Not a `BuildHasher`
  made per call: a default-built seeded hasher (hashbrown's foldhash `RandomState`, std's `RandomState`) can give a
  different hash per instance, and the table would then miss its own entries. `Term::op` hashes, locks one shard,
  finds or `Box::leak`s, unlocks. If the array cannot be built in a `static` initializer, wrap it in a `LazyLock`.
- Reads (`node()`) take no lock.
- No thread-local front cache or lock-free table unless the timed sweeps show lock time (at most 12 scoring threads).
- Nodes are never freed: at most 57 K `Op`s per process, about 1.8 MB at 32 B (`Node` is 32 B: a tag word, `usize`
  and two pointers; a reference's one niche value cannot tag three other variants (U, checked by a test)). The test
  harness runs all tests in one process; the sweep's sum, 1.26 M nodes or about 40 MB, bounds it.
- Determinism: addresses change between runs, but every `Term` map already uses `RandomState`, so no iteration order
  becomes newly nondeterministic; no fixed-seed hasher sees a `Term`; sorts use the structural `Ord`.
- Safe Rust only. `Term` is `Send + Sync` because `Node` holds only `usize` and `Term`.

## Testing and measurement
- Unit tests in rewrite.rs:
  1. Interning: `Term::op(o, a, b)` built twice is pointer-equal; built from 8 threads at once, one pointer per term.
  2. Order pinned: 38 parsed terms (every leaf kind, nested `Op`s, shared prefixes; `parse_term` names only variables below 8, so indices past 8 are checked by a direct assertion), sorted
     by the old derived `Ord` in a throwaway run at the base commit and written into the test as `show()` strings in
     that order; the new `Ord` must sort a shuffled copy back to it.
  3. Text round trip: `parse_term(&t.show()) == t` over the same terms.
  4. `size_of::<Node>() == 32`, `size_of::<Term>() == 8`.
- `cargo test --release --test church_bv` passes; `cargo clippy --tests` adds no warnings.
- Identical outputs: a copy of `docs/runs/2026-10-12/scripts/s3_seq.sh` (old and new exe, salt 1 and 2) that
  differs only in `SWEEP="mines own cold pooled"` (s3_seq.sh hard-codes `mines own pooled`), matching the
  speed runs. Gate: `.tsv` files identical apart from seconds
  columns; logs differ only in timings and their own path, with every `LEMMA_CACHE` line (`loaded/hits/built/saved/
  skipped/bytes`) equal, since the kernel is untouched (the `lemmas.bin` files are deleted when a loop ends, so the
  logs are what is compared); anything else fails.
- Speed: twelve full salt-1 sweeps through `sweep_job.ps1`, old and new alternating. Report median job CPU per arm,
  pair wins out of 6, wall time, load and Defender RTP. Identical sweeps vary about 10%; the profile predicts a
  larger cut (U).
- One samply profile of the new build: the `Term` costs gone, and what leads now.
- Docs: tier-cycle.md's "Where a sweep spends its time" closes its first open direction with the result (including
  the distinct-node probe); a row in `docs/runs/2026-10-12/README.md`.

## Follow-ups (not in this spec)
- `Term` by value in signatures (idiomatic for an 8-byte `Copy`).
- A cheaper hasher than SipHash for `Term`-keyed maps (now hashing one address).
- Memoized `show_cmp` per node pair, or a per-node text-order rank.
- `SigMemo` keyed by node address instead of its own `(o, id, id)` ids.
- The read-through memo view (tier-cycle.md's second open direction), if memo copying still shows.
