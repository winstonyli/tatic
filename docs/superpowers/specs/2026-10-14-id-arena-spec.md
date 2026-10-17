---
status: done
---

# Terms as 32-bit ids in two spaces: spec (draft 3, 2026-10-14)

Status: built through Stage 3 (branches `id-arena-stage2`, `id-arena-stage3`, merged into main at 14f721f and pushed, 2026-10-14). The decisions are summarized in `docs/tier-cycle.md`
("Allocation schemes against the size cost", scheme 4). (V) = read in the code or measured this session; (U) = unverified.

## Goal
Replace the kernel's `Rc` nodes with hash-consed nodes named by 32-bit ids in two spaces. The *region* is a check's
working memory, freed in bulk. The *persistent space* is the thread's long-term memory. The aim is the size cost
of large checks: rule 33's law check costs 240 ns busy per new table entry at n=8 and 491 at n=64 (doc "The rise,
priced by a profile diff"). About 120 ns of that rise is larger maps; the `uses` walks and thinly spread work account
for about 60 each. Freeing the table is another 80 ns per entry. This spec starts with the two id types and the
copy-out function, since they decide what is sound. The rest of the design follows from them.

Non-goals here: compiled code reading ids, parallel checking over a shared persistent space, an in-process
collection of the persistent space. Each is parked below, with what this design leaves open for it.

## What exists (V)
- `kernel::Rc<Expr>` wraps `std::rc::Rc<Node<Expr>>`. The header holds `loose`, `free`, `generation: Cell<u32>` and
  `uses: Cell<u32>`; `Expr` is 48 B and `Node<Expr>` 64 B (`kernel/tests.rs:483-484`), an 80-byte mimalloc block
  with `Rc`'s two counts.
- `hc` (`kernel.rs:849-1344`) is one thread-local `Table` while a scope is open. It holds the node table (16 B entries:
  hash and `Rc`), the memos `inst`, `shifts`, `whnf` and `hnf`, `arg_sets`, and `keep`, which pins the non-canonical
  memo sources. `GENERATION` is nonzero while the table is on and never reused. A node is canonical when its
  `generation` is the current one, which requires all its children to be canonical. Equality skips the walk only for
  two canonical nodes (`PartialEq for Expr`, line 457).
- The per-call caches key by node pointer. In `InferCache`, `types` is `(PtrKey, (u32, u32)) -> Expr`, 64 B an
  entry, and `lows` is `(PtrKey, u32) -> u32`, 24 B. In `ReductionCache`, `nf` is `PtrKey -> Expr`, 56 B.
- Constructors (`pi`, `app`, ...) take `Expr` by value and intern each child through `hc::intern_new`.
- `Drop for Expr` with `LEAF` and `grow_slow` keeps dropping stack-safe.
- `WARM_UP` (3000 calls) and `LARGE` (3000 nodes) switch the table on lazily. Interning costs small checks about 20%
  (`InternScope` doc).
- 79 `InternScope::enter` sites: `search.rs` 31, `machine.rs` 18, `encoding.rs` 16, `rewrite.rs` 5,
  `postulates.rs` 3, `kernel/tests.rs` 3, `proof_scope.rs` 2, `bin.rs` 1.
- About 630 `Expr::` pattern and construction sites: `kernel.rs` 249, `kernel/tests.rs` 206,
  `kernel_soundness_fuzz.rs` 78, `kernel_lazy.rs` 30, `bin.rs` 24, `postulates.rs` 21, the rest under 15.
  `proof.rs` and `jit.rs` have none.
- Pointer identity on kernel nodes:
  - `kernel_lazy.rs:137` (its other address keys, lines 130 and 361-365, are its own `Thunk`/`Val` `Rc`s and stay);
  - `kernel/bin.rs:65`, a pointer-keyed index; its test at 177-190 expects the plain encoding to be larger than the
    interned one;
  - pointer-keyed node counters at `kernel/tests.rs:2622` and `proof/tests.rs:1848`;
  - `Rc::ptr_eq` asserts at `proof/tests.rs:15, 37`;
  - `encoding.rs:1099`;
  - the `record-defeq` pointer maps.
  These become `Ref` identity.
- Behaviour that reads `Rc::strong_count`: `Drop for Expr` (line 523); `infer_rc`'s skip of the memo for an
  unshared node (2524); `postulates.rs:93`; `kernel_lazy.rs:82, 150`. Ids have no counts, so each needs a
  replacement: always memoise, or a per-node "has two parents" bit set when interning finds an existing node.
- The kernel's entries open their own scope: `def_eq` (2180), `infer_in` (2505) and `check_in` (2736). Inside it,
  `hc::large` both interns large inputs and picks the 64 MiB `CHECK_SEGMENT` stack (2737, 2745).
- Terms kept past a scope:
  - `Globals` (`im::Vector<Expr>`; `im::Vector<PExpr>` since Stage 2, as are `Postulates`' parameters);
  - the church_bv caches `CLOSED` (`rewrite.rs:395`), `TREE_LAWS` (`machine.rs:350`) and `PARAMS` (`rewrite.rs:411`);
  - the generation memos `CONSTANTS` and `BODIES` (`encoding.rs` `gen_memo`, emptied when the generation changes);
  - whatever a function that opens a scope returns.

## Measured for this spec (V, 2026-10-14, probe reverted, no patch kept)
Counters in `Rc::new`/`with_ranges` by scope state, and the nodes of the outermost table still alive after it
dropped (by `Weak`):

| Run | Built outside any scope | In a scope, table off | In a scope, table on | Interned at drop | Alive after |
|---|---|---|---|---|---|
| `proof_cost_split` (cmp3d, 300 laws) | 0 | 0 | 3.70 M | 2.98 M | 0.49 M (17%) |
| full salt-1 sweep, 170 child logs, total | 0 | 0 | 13.6 M | 10.8 M | 2.61 M (24%) |
| its largest child (`lib_cmp3d/mine_ref`) | 0 | 0 | 2.43 M | 1.88 M | 0.42 M (22%) |

A positive control (the kernel unit tests) counted nodes outside scopes, so the zeros are real. The miner builds
every node inside a scope with the table on. What follows, and what does not:
1. Outside a region, the miner builds nothing that would land in the persistent space. Other callers (`proof.rs`,
   the fuzzers, the benches, the REPL) were not measured. With the kernel's entries scoped (below), their
   transients stay in regions anyway.
2. Not all nodes go through the table even with it on. 19% (`proof_cost_split`) to 21% (sweep) of those built are
   not in it at the drop. Some are built by direct `Rc::new` calls (16 in `kernel.rs`), which nested scopes may
   also explain (U). The port interns them all, an unmeasured extra cost.
3. "Alive after" is the live set at the end (0.42 M in the largest child). It is not the copy-out volume. That volume
   is the sum over every outermost `scoped` exit and every store, including results a caller then drops, and it is
   unmeasured. Stage 2's counter measures it.

## Design

### Spaces
- **Persistent space**, one per thread: append-only, hash-consed, never freed while the process lives (a process
  boundary is the collection; the driver already runs each child as its own process). Its table, nodes and side
  arrays only grow.
- **Region**, at most one open per thread: opened by the outermost scope, hash-consed, freed in bulk when that scope
  closes. Nested scopes join the open region, as `hc::DEPTH` does now. Each opening takes a fresh per-thread *region
  generation* (u32, never reused; overflow panics). Closing the region clears the node vector, side arrays, table,
  memos, persist memo and twin map, and keeps their capacity. While no region is open, every region handle is dead.
- Outside any region, constructors build in the persistent space.

### Refs and nodes
- `Ref(u32)`: bit 31 says region (1) or persistent (0), and bits 0-29 index that space's node vector. Bit 30 is
  clear in every `Ref`, so an `inst` argument-list id can be a `Ref` (one argument) or a list id with bit 30 set,
  in one u32. Each space holds up to 2^30 nodes (39 GB at 36 B, never reached).
- `Node<C>` is a `Copy` enum shaped like today's `Expr`, generic in its child type `C`:
  - `Node<Ref>` is stored. It is 24 B (U until a `size_of` assert): the largest variant, `J`, has five 4-byte
    children, plus the tag.
  - Per node, side arrays hold `loose`, `free` and the `uses` slot (12 B).
  - So 36 B per node against 80 today.
  - A two-child layout of 12 B, with separate storage for the 3- and 5-child formers, is parked until the enum is
    measured.
- The memos key by `Ref`. With id keys:

  | Memo | Entry now | Entry with ids |
  |---|---|---|
  | node table | 16 B (hash, `Rc`) | 8 B (u32 hash, `Ref`) |
  | `inst` | 32 B | 16 B (`Ref`, args id u32, depth) → `Ref` |
  | `lows` | 24 B | 12 B |
  | `InferCache.types` | 64 B | 16 B |
  | `ReductionCache.nf` | 56 B | 8 B |

  `keep` and pinning go: an id cannot be reused while its space lives.

### The two id types
- **`Expr`**: a handle for Rust code, 8 B: a `Ref` and the region generation it was made in (ignored for a persistent
  `Ref`). It is `Copy` and `!Send`/`!Sync` (`PhantomData<*const ()>`), since each space is per thread.
  - Every conversion from a handle to a `Ref` checks it: a region `Ref` whose generation is not the open region's
    panics (*dead handle*). That covers the handles `infer` reads out of `Ctx` (`ctx_lookup`) and out of a
    `Postulates`'s parameters, not only a call's arguments. Kernel internals then work on raw `Ref`s read from
    nodes, which are valid whenever their node is. A dead handle can never name another term; it fails.
  - `Debug` on a dead handle prints `<dead handle>` rather than panicking, so an `assert_eq!` reports instead of
    aborting.
  - `e.node()` returns `Node<Expr>`, so patterns match a copy: `match e.node() { Node::App(f, a) => .. }`.
  - `Eq` compares canonical `Ref`s (after the twin map below). `Expr` has no `Hash`: a persistent `Ref` at or above
    `W` reads as its region twin until the region closes, so a hash taken in the region would change. Nothing hashes
    `Expr` today (V: no `HashMap`/`HashSet` keyed by it in `src` or `tests`). Keys are `PExpr`.
- **`PExpr`**: a persistent `Ref`, 4 B, `Copy`, `!Send`.
  - It is valid for the thread's life, and its `Eq` and `Hash` are those of the `Ref`, so stable.
  - `Expr::from(p)` is free. The only way from `Expr` to `PExpr` is `persist`.
- Long-lived stores hold `PExpr`: `Globals`, `CLOSED`, `TREE_LAWS`, `PARAMS`, `lemma_cache` records. That is a
  convention the types make easy: a store of `Expr` still compiles, and its stale handles fail at run time on first
  use.
  - Stores filled from inside a closure are the same case: a builder pushing into `&mut Postulates`, or `memo`
    inserting into `CLOSED`. `Escape` sees only return values.
  - A region lifetime, `Expr<'r>`, would make all of these compile errors, since a `thread_local` needs `'static`.
    It is still rejected, as in §64, because the lifetime spreads through every proof record and builder signature.
    That leaves stores to run time, and Stage 3's gate that every test passes.

### The copy-out function
`persist(e: Expr) -> PExpr`:
- Copies the region nodes reachable from `e` into the persistent space bottom-up and interns each there. Nodes
  already persistent are shared, not copied.
- A per-region memo maps a region `Ref` to its persistent copy, so persisting overlapping terms copies each node once.
- Cost: linear in nodes not yet copied. The total is unmeasured (above).
- It walks under `grow`, as every traversal does.
- On a persistent `e` it is the identity. It can run with the region open: the region keeps working, and the
  persisted copy is valid after it closes.

*Twins.* While the region is open, a persisted node and the region node it was copied from are the same term under
two `Ref`s. The region records the reverse map, persistent `Ref` to region twin, for every node it copied. Let `W` be
the persistent length when the region opened. Reading a handle whose `Ref` is persistent and at least `W` maps it to
its twin; otherwise reading costs one compare. Every persistent node at or above `W` was copied from this region (the
region is the only builder while it is open), so every one has a twin.

### Interning rule
One rule for every node, leaves included:
- A node whose children are all persistent is looked up in the persistent table first, counting only hits below
  `W`. A hit at or above `W` is a copy whose twin is in the region table, so the region lookup finds it.
- Otherwise the node is looked up, or built, in the region.
- With no region open, everything goes to the persistent space (`W` is its whole length).

The cost: a node over persistent children (leaves included) takes two probes on a persistent miss. Leaves were 0.74 M
of the 7.67 M builder interns in `proof_cost_split` (doc "Who looks up what").

*Invariant R (what internals see).* Kernel internals never hold a persistent `Ref` at or above `W`:
- handle reads map such a `Ref` to its twin;
- persistent lookups from the region ignore those hits;
- a region node's children were canonical when it was built;
- a persistent node below `W` has only children below `W`.

*Invariant I (no duplicates).* No two `Ref`s that a kernel internal can see name the same term.
- Persistent nodes are added in two ways only: outside regions, interned; or by `persist`, whose copies above `W` are
  mapped back to their twins on every handle read.
- A region node is built only when its structure is in neither table at that moment. A node with a region child
  cannot be persistent, since a persistent node's children are persistent.
- Below `W`, the persistent space was complete before the region opened.

So within an open region, two canonical `Ref`s are equal exactly when they are the same id, and `==` is an id
compare. The `canonical()` bit, the node `generation` and the structural fallback in `PartialEq` are deleted.

### Soundness
The kernel's judgments are about the terms that ids name when `check` runs. It is sound if every id names the term it
was built as, which these give:
1. Both spaces are append-only while they live; a node never changes.
2. A region `Ref` reaches Rust code only inside a generation-checked handle, so it never outlives its region
   unnoticed.
3. Persistent nodes have only persistent children (`persist` copies bottom-up; persistent interning asserts it).
4. Handles are `!Send`, so a thread's ids never reach another thread's spaces.

Completeness of interning (Invariant I) only affects speed: a missed duplicate makes `conv` recurse into the children
or misses a memo. It never makes a judgment wrong. One thing changes: the kernel's ids index arrays (bounds-checked),
where it used to follow pointers.

### Kernel internals
- Public entries (`check_in`, `infer_in`, `def_eq`, `whnf`, `normalize`, the constructors) take handles, read the
  thread's spaces once, and call internal functions that take `&Spaces` and `Ref`s.
- The checking entries are `scoped` themselves, as they open `hc::Scope` today. A `check_in` outside a region
  therefore frees all its transients and returns `Result<(), String>`, with nothing to copy. `infer_in`, `whnf` and
  `normalize` called outermost copy their one result out.
- The node table stores a u32 hash. Probes rebuild a 64-bit hash from it (`h as u64 * K` for an odd constant `K`),
  because hashbrown takes its 7-bit tag from the top bits. A zero-extended u32 would give every entry tag 0 and turn
  every probe into node reads.
- After a region closes, a table or memo that the region used to under a quarter of its capacity is reallocated
  small. hashbrown's `clear` costs time in the capacity (`raw/mod.rs:872-885`), so keeping a large capacity would
  charge every small later region (a `cong1` outside a region) for the largest one.
- `CHECK_SEGMENT` needs a new trigger in place of `hc::large`: the input's distinct-node count, now a walk of `Ref`s
  with a bitset, bounded at `LARGE` as now.
- `Spaces` allocates through `&self` (`UnsafeCell`, single-threaded). Node reads return `Node<Ref>` by value, so no
  borrow is held across an allocation that grows a vector. That is the one `unsafe` contract, and it is local to
  `Spaces`.
- `uses` keeps its per-node slot, now in a side array, and behind the slot the per-scope `bounds` memo (since 1bb3a5c,
  doc "The slot in front of bounds"), keyed by `(Ref, depth)`. `lowest_loose` keeps its `(Ref, depth)` memo (it is
  not compositional; doc "Why `lowest_loose` cannot move into the node header").

### Scopes: `scoped` and `Escape`
Functions open scopes and return terms. The kernel's own builders do it too: `cong1`, `trans_proof` and `cong_n`
(`postulates.rs:311-369`) open a scope "of their own outside one" and return the proof they built. Called outside a
region, they would return a dead handle. Copying each such result out by hand at each of the 79 sites is the
special-casing to avoid. One mechanism instead:
- `kernel::scoped(f: impl FnOnce() -> R) -> R where R: Escape` runs `f` in the open region, or in a new one.
- When this call opened the region, it applies `R::escape` to the result (copy-out of every term in it) before
  closing. When nested, it does nothing, which is the miner's case (it builds everything inside scopes, measured).
- `trait Escape { fn escape(self) -> Self; }` is implemented for:
  - `Expr` (`persist`, returned as a handle) and `PExpr` (identity);
  - primitives, `String` and `()` (identity);
  - `Option`, `Result`, `Vec`, `Box` and tuples up to 6 (element-wise).
  A type holding terms with no impl fails to compile when it is returned from `scoped`. That is a compile-time check
  on stable Rust. A user struct with terms implements `Escape` by hand.
- `InternScope` and its guard pattern are deleted. The 79 sites become `scoped(|| ..)`, and the optional `NO_SCOPE`
  scopes in `encoding.rs` become plain `scoped` (see below).
- What `scoped` cannot see: a term stored mid-region into a long-lived place (a `thread_local` cache, a field). Those
  stores hold `PExpr`, and a store of `Expr` is caught at run time.

### Generation memos
`intern_generation()` becomes the region generation, and 0 while no region is open (persistent handles, valid
forever). So `gen_memo` (CONSTANTS, BODIES) keeps working unchanged. Its entries are rebuilt per region and never
copied out.

The `NO_SCOPE` switch in `encoding.rs` (an A/B without interning) has no meaning once everything interns, and is
deleted.

### Deleted by the port
- `kernel::Rc` and `Node<T>`'s `generation`, `canonical()`, `PtrKey` and `PtrHasher` (u32 keys hash with the
  existing `Fx`, U).
- `Drop for Expr`, `LEAF`, and `grow_slow`'s drop path; `grow` stays for traversals.
- `WARM_UP`, `CALLS`, `canonical_inputs`, `canon`, `keep`/`pin`, and the scope-drop cost (80 ns per entry).
  `LARGE` and an `exceeds` over `Ref`s stay, for the stack trigger only.
- `hc_probe`'s simulated table: ids are the real one.

## Stages
**Stage 1: falsify the speed claim (throwaway; estimated one to two days, with the re-profile and three arms).**
- **Done 2026-10-14: continue.** The gate passed (0.86). At n=64, (b) is 20% below (a) and (c) is 7% below. The rise
  with n is unchanged in every arm. Numbers in tier-cycle.md, "Stage 1 result".
- Record, from rule 33's law check at n=8, 16, 32 and 64, the trace of table and memo operations, with nodes
  numbered densely:
  - interns with their children;
  - the `hc` memos' gets and puts (`inst`, `shifts`, `whnf`, `hnf`, `arg_sets`);
  - the per-call caches' gets and puts (`InferCache.types`, `.contexts`, `.lows`, `.context_of`; `ReductionCache`);
  - the `uses` and `lowest_loose` calls.
  The per-call caches hold the largest entries (`types` 64 B), so leaving them out would hide the biggest shrink.
  - `Rc` clones and drops at those sites, so (a) pays the refcount traffic that ids remove.
- Replay it three times, timing per new node-table entry:
  - (a) today's layout: `Rc` nodes allocated through mimalloc in trace order, with today's maps and key types;
  - (b) the id layout above, with `Ref`-keyed maps;
  - (c) a hybrid: today's `Rc` nodes, each given a dense u32 id when interned, with the memos keyed and valued by
    those ids (a per-scope `Vec<Rc>` maps an id back).
    - It shrinks the maps without the port. It cannot shrink the nodes or drop the per-node free.
    - The id needs 4 header bytes, and the header has none free (`uses` fills the padding). So it either replaces a
      field or moves the block from mimalloc's 80-byte class to 96. The replay uses the 96-byte block, the honest
      case.
- If (c) gets most of (b)'s gain, the hybrid is the cheaper end, and this spec is rewritten around it.
- What the replay misses:
  - The reducer's own node reads (the thinly spread 60 ns), which understates (b).
  - The real allocation layout (trace order only approximates
  mimalloc's interleaving with other allocations).
  - The port's own costs (the double probe, the twin check, the handle check, interning the 19-21% that bypass the
    table today), which overstate (b).
  So it is a filter, not a prediction. A clear loss stops the port; a gain only justifies the next step.
- **Validity gate:**
  - First re-profile rule 33's rise on large pages. The 120 ns was measured before they were on, and they took about
    42 ns per entry off at n=64.
  - (a)'s rise must then be within ±30% of that profile's map plus `uses` cost (about 180 ns before large pages),
    since the trace includes the `uses` walks.
  - If not, the replay does not reproduce the effect: void, not fail.
- **Stop:** if neither (b) nor (c) is 15% or more below (a) per entry at n=64, record the numbers in tier-cycle.md
  and stop.
- **Continue:** otherwise, to a narrower real prototype before Stage 3.
  - The port of `shift`, `instantiate`, `uses` and `lowest_loose` alone onto ids, on a branch.
  - It is driven by the same law check, with `Rc` terms converted in and out at its boundary.
  - It is timed against `main`.
  - **Dropped (2026-10-14), before it was built:** it cannot discriminate. Callers use its results as `Rc` at once
    (`kernel.rs` 1900, 1939, 2624-2635), so its boundary builds every new node twice. That cancels Stage 1's intern and
    node-build gains, and Stage 1's per-op costs leave about zero net at n=64 (`lowest_loose` +20, memo get +15, memo
    put -26, `uses` -11 ns per entry). Stage 2 goes first instead, and measures the copy-out volume; the port decision
    rests on that and Stage 1's replay (plan `docs/superpowers/plans/2026-10-14-id-arena-stage2.md`).

**Stage 2: the two id types, `persist`, `scoped` and `Escape` on today's representation (kept; additive).**
- `PExpr` is a newtype over today's `Expr`, made only by `persist`: a clone, plus a counter of reached nodes in the
  current generation when a feature is on.
- `scoped` with `Escape` replaces `InternScope` at the 79 sites. Here `escape` is `persist`.
- `Globals` and the church_bv stores move to `PExpr`.
- Behaviour is unchanged and timings stay within noise.
- It fixes every store's and every scoped function's types before the port, and the counter gives the true copy-out
  volume (without stale memo entries).
- Stage 3 keeps the signatures.
- **Done (2026-10-14, branch `id-arena-stage2`, commits 343a34f-108a704; plan
  `docs/superpowers/plans/2026-10-14-id-arena-stage2.md`).** Sweep outputs identical on both salts;
  `proof_cost_split` CPU median 3.98 → 3.94 s (won 5 of 8). Copy-out volume, `stale` and `outside` 0 on both:
  `proof_cost_split` 1,712 `persist` calls copying 493,753 nodes (17% of the 2.98 M interned; the probe's 0.49 M alive
  after); a salt-1 sweep 9,620 calls copying 1.55 M (14% of 10.8 M). Doc "Id arena Stage 2" has the tables.
  Departures from this section:
  - The counter counts by *region* (outermost scope, lazy or not), not generation: 19-21% of a scope's nodes never
    enter the table, and in the arena every node built in a region is a region node.
  - `Postulates` holds `PExpr` too (`PARAMS` and `PRELUDE` keep one for the thread's life).
  - `NO_SCOPE` and the other A/B toggles stay, as `if c { scoped(body) } else { body() }`, until the port.
  - The kernel entries open their scope through the same `hc::scoped`, so an outermost `infer_in` persists its result.

**Stage 3: the port, on a branch.**
- `Spaces`, `Node`, the handles and the kernel internals on `Ref`s.
- The 630 sites: patterns become `match e.node()`, and raw `Expr::X(..)` construction becomes constructor calls.
- `kernel_lazy` reads through `node()`.
- Gates:
  - all tests and both kernel fuzzers pass;
  - a dead-handle test panics;
  - a salt-1 sweep's tsv files are identical apart from the seconds columns;
  - rule 33 at n=8-64, `proof_cost_split` and the sweep job (`sweep_job.ps1`) are timed A/B against `main` with peak
    commit;
  - the gcd small-proof benches are within 10%, after they open a region per iteration.
- **Done (2026-10-14, branch `id-arena-stage3`: 6833fb9 harness, 3be0e79 Phase A, 1166b0e `spaces.rs`, ff173a6
  Phase B; plan `docs/superpowers/plans/2026-10-14-id-arena-stage3.md`).** Every gate passes. Sweep outputs are
  identical on both salts for both phases; lib tests 371 → 374, the rest unchanged; the dead-handle tests pass.
  Against 6833fb9 (RTP off, load 9-24%): `proof_cost_split` CPU median 3.73 → 2.54 s (won 8 of 8); rule 33's law
  478-491 → 252-315 ms at n=64 and 50-54 → 21-25 ms at n=8 (every pair won at n = 8-64); salt-1 sweep job CPU
  51.5 → 51.1 s, peak commit 578 → 514 MB (largest process); gcd benches 0.43-0.59 of base. Doc "Id arena Stage 3"
  has the tables. Departures from this section (the plan has each one's reasoning):
  1. Two phases: the API port on `Rc` storage first (A), then the storage swap (B).
  2. Internals hold `Expr` handles and every read resolves, instead of raw `Ref`s inside a checked public call.
     Parked: raw-`Ref` walks for the hottest walks, if a profile shows `resolve`.
  3. `shared` is a parent count bumped at build and saturating at 2, never lowered, so a persistent node's count only
     rises across checks.
  4. `ReductionCache` and `eq_noting` are deleted: `whnf`, `hnf` and `nf` live in the region's memos, and `==` is an
     id compare.
  5. Twin functions merge (`whnf`, `nf`, `conv`).
  6. The memos are on outside a region too; the next close empties them.
  7. `Memos` is a `RefCell` beside the nodes' `UnsafeCell`.
  8. Probes: `take_built` counters replace `hc_probe`; `instantiate_memo` and `rename_*` are deleted; `DEFEQ_LOG`
     keeps persisted terms.
  9. The `copy-volume` feature is deleted.
  10. `with_ranges` is deleted; ranges come from the children at build time.
  11. `WARM_UP` and the lazy table go: every node built in a region is interned. Small proofs got faster, not slower.
  12. `hc::exceeds` walks with an `IdSet`, not a bitset. Parked: a bitset, if the walk shows.
  13. Memo skips follow parent counts in Phase A too, so A's timing is not the API's cost alone.
  14. Every `benches/proofs.rs` iteration runs in its own region, not only the gcd ones.
  15. `Spaces::from_key` is named `expr_of`, since it reads the epoch through `self`.

## Risks
- Every node read becomes an index into a thread-local space: bounds check plus base load. Internals take `&Spaces`
  once, so the thread-local cost is per public call. The index cost is unmeasured (U); Stage 1 times part of it.
- Terms built by constructors outside any region (benches, unit tests, `proof.rs` callers) go to the persistent
  space and are never freed in-process. The checks themselves free their transients, since the entries are
  `scoped`. The miner builds no terms outside regions (measured). Long benches should build inside `scoped`.
- A store that keeps `Expr` instead of `PExpr` fails at run time, not compile time. Returns are checked at compile
  time by `Escape`.
- An outermost `scoped` that returns a large term copies it out, even a proof the caller then discards, and the copy
  stays for the process's life. The volume is unmeasured until Stage 2's counter. If it is large, the outermost
  scope moves out to a caller that returns less.
- Region overflow at 2^30 nodes, and generation overflow at 2^32 regions, panic.
- A panic unwinding through `scoped` closes the region in its guard's `Drop`, without `escape`. Nothing is copied,
  and handles from it are dead, as on a normal close.

## Parked
- *In-process collection of the persistent space* (copy the live set from explicit roots at a quiescent point). Not
  needed while children are processes. `PExpr` stores are the roots it would need.
- *Shared frozen persistent space for parallel checking.* Persistent ids would index a `Sync` frozen space. This
  design keeps it possible: persistent nodes only point to persistent nodes.
- *Compiled code reading ids.* Region nodes are a flat vector, so linear memory could map them.
- *`lemma_cache` keyed by `PExpr`.* Ids are stable only within a process; files still need text.
- *Variable-length nodes* (12 B for two children).

## Decisions for you
- **D1, escape check for returns. Decided 2026-10-14: option 1.**
  1. `scoped` with a hand-implemented `Escape` trait, above. (Recommended; chosen.) Pro: stable Rust; the outermost call
     copies out by itself. Con: a manual impl per term-holding return type.
  2. An auto trait `RegionFree` (nightly `auto_traits`, `negative_impls`). Pro: no impls to write. Con: the crate's
     first unstable features, and it only rejects; it does not copy out.
  3. Run time only, keeping `InternScope` guards. Pro: no site changes. Con: the kernel's own `cong1`/`trans_proof`/
     `cong_n` return dead handles outside a region, so they still need per-site copies.
- **D2, build order. Decided 2026-10-14: option 1.**
  1. Stage 1 first. (Recommended; chosen.) Pro: one to two days decide whether the port, or the cheaper hybrid (c), is
     worth building. Con: throwaway code.
  2. Stage 2 first. Pro: it is what was asked to start with. Con: churn if Stage 1 fails.

## Adversarial review (5 rounds)
- **Before the draft (a measurement).** Whether anything is built outside scopes, since that would land in the
  persistent space forever. Probed: no.
  - Also rejected before writing: copying out lazily at region close through a slot table. A slot's `Hash` would
    change at close. Eager `persist` with twins replaced it.
- **Round 1 (self: contradictions, missing steps).**
  - `cong1`, `trans_proof` and `cong_n` open the outermost scope and return terms, so they would return dead
    handles. This led to `scoped` and `Escape`, which replaced D1's run-time-only default.
  - Nothing hashes `Expr` (checked), so `Expr` gets no `Hash`.
  - A persistent probe from a region could return a copy at or above `W`. It now counts only hits below `W`, and
    Invariant R is stated.
  - Stage 1's trace lacked the per-call caches (the largest entries). Added, with a validity gate.
- **Round 2 (self: sizes, encodings, options not considered).**
  - The node is 24 B as an enum, not 28.
  - `inst`'s argument-list id needs a tag bit beside a `Ref`: 30-bit indices.
  - Pointer-identity sites were missing.
  - Not considered: dense u32 ids on today's `Rc` nodes, which shrink the maps without the port. Added as Stage 1
    arm (c), with its header cost (the 96-byte class).
- **Round 3 (an independent reviewer, Sonnet, with the code).**
  - Region handles inside `Ctx` and `Postulates` skipped the "once per call" check. Now every handle-to-`Ref`
    conversion is checked.
  - `Escape` misses stores made from inside closures. Recorded; `Expr<'r>` reconsidered and still rejected.
  - The checking entries open their own scopes; they are now `scoped`.
  - "At most 0.4 M copied out" was unsupported: withdrawn, to be measured.
  - 19-21% of nodes bypass the table today, so "always interning is free" was wrong.
  - hashbrown's `clear` costs time in the capacity: shrink after close.
  - A zero-extended u32 hash gives every entry tag 0: re-spread.
  - Stage 1's gate compared against the wrong cost (it omitted `uses`, and was measured before large pages), and
    the replay misses refcount traffic, layout and the port's own costs. Now a one-sided filter with a narrower
    real prototype after it.
  - `strong_count` users, more pointer sites and the `CHECK_SEGMENT` trigger were missing. A wrong (V) claim about
    `kernel_lazy`'s address keys was fixed.
  - The reviewer found no hole in Invariants I and R.
- **Round 4 (self: full re-read of draft 3).** Seven contradictions or stale claims left by the fixes: `LARGE` both
  kept and deleted; `NO_SCOPE` both converted and deleted; a duplicated replay caveat; "never freed" against the
  scoped checks; "bounded by measured escapes" after the bound was withdrawn; 12 against 16 B; Stage 1's
  duration.
- **Round 5 (self: re-read of the changed passages).** Nothing material.
