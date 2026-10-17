---
status: done
---

# Id arena Stage 3: terms as 32-bit ids in two spaces (plan)

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. The
> tasks depend on each other, and A2 and B2 are atomic switches that no subagent can hold in context, so execute
> inline (Opus controller). Only B1 (`spaces.rs`, complete code below) may go to one implementer; per WORKING_STYLE
> that is Sonnet, since its check needs judgment about panics. Steps use checkbox (`- [ ]`) syntax for tracking.

**Status:** done through Task 6 Step 5 on branch `id-arena-stage3` (2026-10-14; ff173a6 Phase B, docs commit after
it). Every gate passes; results in `docs/tier-cycle.md` "Id arena Stage 3". Merged into main (fast-forward to 14f721f) and pushed, 2026-10-14.

**Goal:** Replace the kernel's `Rc` nodes with hash-consed nodes named by 32-bit ids in a per-thread persistent space
and a per-check region (spec, "Design"), keeping the public signatures Stage 2 fixed, and measure the result against
Stage 2 on rule 33's law check at n=8-64, `proof_cost_split`, a sweep's CPU and peak commit, and the gcd benches.

**Why (decided 2026-10-14, the user's "1" after Stage 2):** Stage 1's replay gave the id layout 20% at n=64 and 33% at
n=8 per table entry. Stage 2 measured the copy-out the arena adds: 17% of the interned nodes for `proof_cost_split`, 14%
for a sweep, and no stale terms. The port is the only way to learn its net.

**Architecture.** Two phases on one branch, each ending at a behaviour gate:
- **Phase A, the handle API on today's storage (Tasks 2-3).** `Expr` becomes a struct: one `std::rc::Rc` to a header
  that holds the ranges, the `hc` fields and a generic `Node<Expr>`. The enum is `Node<C>`, generic in its child type.
  Every term is now a node, so the root/child split (`Expr` against `Rc<Expr>`) is gone.
  - Code reads a term with `e.node()` (or `s.node(e)` inside the kernel) and builds one with `mk(Node::X(..))` or the
    named constructors.
  - Kernel internals take `s: &Spaces`, a zero-sized stub in Phase A.
  - Every pointer-keyed map keys by `Key` (Phase A: `PtrKey`, which holds the node; Phase B: `u32`).
  - All ~630 `Expr::` sites are ported here. Behaviour is unchanged, and the sweep's outputs stay identical.
- **Phase B, the storage swap (Tasks 4-6).** `spaces.rs` holds the two spaces (Task 4, standalone, with unit tests).
  Then `Spaces` becomes the real arena behind the same internal API, and `Expr` becomes a `Copy` handle `(Ref, region
  generation)`.
  - The `hc` table, the generation and canonical machinery, `ReductionCache`, `eq_noting`, `Drop` and `PtrKey` are
    deleted.
  - The memos move into the region and empty when it closes.

**Tech stack:** Rust (nightly, edition 2024), hashbrown 0.16 (`HashTable`, `HashMap`), im, stacker. No new dependencies.

**Spec:** `docs/superpowers/specs/2026-10-14-id-arena-spec.md` (local, git-excluded), "Design" and "Stage 3". Where
this plan departs from it, it says so ("Departures"), and Task 6 records each departure in the spec.

## Global Constraints

- **Work in a worktree:** `git worktree add ../tatic-s3 -b id-arena-stage3 fd70bb7` (the Stage 2 branch's head), with
  `CARGO_TARGET_DIR=target/s3` on every cargo call there. Worktree files are CRLF: change them with the Edit tool, or
  use `\r?\n` in any regex. `id-arena-stage2` is unmerged and unpushed, so this branch carries it.
- **Behaviour unchanged, both phases:** every test that passes at Task 1's commit passes after A2 and after B2, except
  the tests this plan deletes by name (each listed in its task, with why). Both kernel fuzzers (`kernel_fuzz`,
  `kernel_soundness_fuzz`) run in the default `cargo test`. A salt-1 and salt-2 sweep (`SWEEP="mines own pooled"`):
  - the `.tsv` files are identical apart from seconds columns;
  - every other differing file is a log that differs only in timings, its own path, and (Phase B) `LEMMA_CACHE ...
    bytes=`;
  - a lemma-cache file may differ only in its binary encoding's node sharing, with the `LEMMA_CACHE` lines'
    `loaded/hits/built/saved/skipped` counts equal.
  - Any other difference fails the gate.
- **Naming:** the region generation is `epoch` in code (fields, parameters, `Spaces::epoch()`), because `gen` is a
  reserved keyword in edition 2024. The public `intern_generation` keeps its name.
- **One term type.** No `Rc<Expr>`, no `kernel::Rc`, no raw `Ref` outside `spaces.rs` and `Spaces`' kernel-side
  methods. Kernel internals hold `Expr` handles; each read resolves its handle (spec departure 2).
- **Kept signatures:** the public functions that take or return terms keep the signatures Stage 2 fixed (`PExpr`,
  `persist`, `scoped`, `Escape`, `Globals`, the constructors, `check_in`, `infer_in`, `def_eq`, `whnf`, `normalize`,
  `shift`, `typecheck`, `Postulates`' methods). New public items: `Node`, `mk`, `Expr::{node, loose, free, shared}`,
  `node_key`. Removed: `kernel::Rc`, `loose_of`, `free_of` (now methods), `same_shape` (now `Node::same_shape`).
- **No compat shims, superseded code deleted** (each listed per task).
- **Builds:** `-j 8`. Runs pinned: `cmd //c start "" //b //belownormal //affinity FFF //wait <exe> ...`, or
  `cpu_ab.ps1`/`sweep_job.ps1` (which pin themselves). Before any timing, report CPU load (`\Processor(_Total)\%
  Processor Time`, two samples) and Defender's `RealTimeProtectionEnabled`. Never change Defender.
- **Python:** never run python that reads stdin; write a file and run `python -P f.py < /dev/null`.
- **Commits:** one per task. Write the message through PowerShell, `@'...'@ | Out-File -Encoding ascii
  "$env:TEMP\msg.txt"`, then `git commit -q -F "$env:TEMP\msg.txt"`. Check `git diff --cached --stat` first, and delete
  msg.txt from Bash after (`rm -f "$(cygpath -u "$TEMP")/msg.txt"`). End with `Co-Authored-By: Claude Opus 5.5
  <noreply@anthropic.com>`. **No push and no merge** without the user's go-ahead.
- **Leave alone:**
  - the untracked `tests/ring_spike.rs` and `tests/ring_loop_spike.rs` in main;
  - other sessions' processes (a `cargo test --lib -j 4 dag_` from another session was seen 2026-10-14);
  - `$TEMP` files that aren't this plan's (`$TEMP/kk/s2_*` stay).

## Departures from the spec (Task 6 records each in the spec)

1. **Two phases.** The spec has one port. Here the API port (A) runs on today's `Rc` storage, behind a behaviour gate,
   before the storage swap (B). A bug then shows up either as a port slip or as an arena fault, not as both at once,
   and A's informational timing separates the API's cost from the arena's.
2. **Internals hold `Expr` handles, not raw `Ref`s.** The spec checks a handle once per public call and runs the
   internals on raw `Ref`s. That splits every internal signature into two term types. Here every read resolves its
   handle: a region `Ref` is one generation compare, and a persistent one is one compare against `w`.
   - Gain: one term type and no `Ref`s outside `Spaces`.
   - Cost: a compare and a branch per node read, which B's timing includes.
   - Parked: moving the hottest walks (`inst_rec`, `uses`, `conv_whnf`) to raw `Ref`s, if a profile shows `resolve`.
3. **`shared` counts parents in both phases.** `strong_count > 1` (`infer_rc`, `abstract_frees_in`, `kernel_lazy`)
   becomes a per-node parent count, bumped when a node is built over the child and saturating at 2. It no longer counts
   Rust handles. Only the memos' hit rates can change, never an answer: a node reached twice has two parents or a
   shared ancestor, except when the same node is a root of two separate calls into one `InferCache`. In Phase B a
   region build bumps a persistent child's count too, and nothing lowers it at close, so a persistent node's
   `shared` can only rise across checks. That over-counts on purpose. Over-counting only adds memo entries, while
   counting just region-local parents would read a persistent node used twice in one check as unshared, and skip the
   memo that keeps DAG walks linear.
4. **`ReductionCache` and `eq_noting` are deleted (B).** The spec shrinks `ReductionCache.nf`'s entries. Here:
   - `whnf`, `hnf` and `nf` live in the region's memos, which are sound across calls because reduction reads no
     context;
   - `unequal` goes, because `==` is an id compare under Invariant I;
   - `conv` compares ids, then weak head normal forms.
5. **Twin functions merge:** `whnf_impl`+`whnf_rc`, `nf_impl`+`nf_rc` and `conv`+`conv_rc` each become one function.
   Every term is a node, so the "child already held as `Rc`" distinction is gone. A2 does this, so the merged
   functions' memo traffic shows in A's timing.
6. **The memos are on outside a region too (B).** The spec has them off there. Every public kernel entry is `scoped`,
   so the only memo use outside a region is a public `shift`/`instantiate` from a builder. Entries made then name
   persistent nodes, which never die, and the next close empties them. One code path, no "is a region open" test per
   lookup.
7. **`Memos` sits in a `RefCell` beside the nodes' `UnsafeCell`.** The spec says only "`Spaces` allocates through
   `&self`". The nodes stay in the `UnsafeCell` (the hot reads, no borrow flag). The memos are borrowed briefly
   and never across a call back into the kernel, so a `RefCell` makes their aliasing checked at no design cost.
8. **Probes.** `hc_probe`'s simulated table is replaced by real counters (`take_built`, feature `record-defeq`, counting
   `mk` calls and new nodes). `take_hc_inst`, `instantiate_memo` and `rename_*` (the option C probe) are deleted with
   their probe printouts. `DEFEQ_LOG` keeps persisted terms so its readers can use them after the check's region
   closes.
9. **The `copy-volume` feature is deleted (A).** Its numbers are recorded (doc "Id arena Stage 2"), and its header
   fields block the new layout.
10. **`with_ranges` is deleted.** Ranges come from the children at build time, three to six `max` operations.
11. **Small proofs pay the interning.** `WARM_UP` and the lazy table go: every node built in a region is interned (the
    spec's "the port interns them all"). The gcd bench gate (spec: within 10%) is where this shows.
12. **`hc::exceeds` walks with an `IdSet<Key>`, not the spec's bitset.** It is one walk per large check, and a
    bitset over region indices would need a second path for persistent `Ref`s. Parked: a bitset, if the walk shows in
    a profile.
13. **`shared` changes what the memos skip in Phase A too.** Today a node in the `hc` table has `strong_count >= 2`
    (the table holds one), so `infer_rc`, `abstract_frees_in` and `kernel_lazy`'s `memo_on` memoise nearly every
    interned node. With parent counts they memoise only nodes with two parents. Answers and messages don't change,
    but Phase A's timing mixes the handle's cost with this change, so A's numbers are not "the API's cost" alone.

## File map

| File | Change |
|---|---|
| `src/kernel.rs` | A: `Node<C>`, `Expr`/`Header`, `Spaces` stub, `mk`, ported internals, `copy_volume`/`hc_probe` hooks, `LEAF` and `Drop for Expr` gone. B: `Expr` handle, `PExpr(Ref)`, kernel-side `Spaces` methods, `hc` on `Memos`, `ReductionCache`/`PtrKey`/`PtrHasher`/generation machinery gone |
| `src/kernel/spaces.rs` | B1: new. `Ref`, `Space`, `Spaces`, `Memos`, `IdHasher`, unit tests |
| `src/kernel/hc_probe.rs` | A: deleted |
| `src/kernel/postulates.rs` | A: `abstract_frees_in` on `map_kids`; `FreesMemo` keyed by `Key`; leaf builds through `mk` |
| `src/kernel/bin.rs` | A: `children`/`tag`/`write` on `Node`; index by `node_key`. B: its sharing test's sizes |
| `src/kernel/tests.rs` | A: ported (206 `Expr::` sites, 94 `Rc::new`); 2 tests deleted. B: deletions and ports listed in Task 5; 2 dead-handle tests |
| `src/kernel_lazy.rs` | A: `KRc<Expr>` → `Expr`, matches on `node()`, `memo_key` by `node_key`, `strong_count` → `shared` |
| `src/proof/tests.rs`, `src/proof/instance.rs` | A: pattern sites; `ptr_eq` → `node_key` equality; `dag_size` → `term_sizes` |
| `tests/kernel_fuzz.rs`, `tests/kernel_soundness_fuzz.rs` | A: leaves and the `count_nodes`/`nth_subterm`/`replace` walks on `Node` |
| `tests/church_bv/*.rs`, `tests/proof_scope.rs`, `benches/*.rs`, `examples/*` | A: pattern sites; `COPYVOL` and `hc_probe` printouts; `intern_lookup_vs_rc_new` deleted. B: two identity asserts; gcd benches in `scoped` |
| `tests/church_bv/rewrite.rs` | Task 1: `law_time` |
| `Cargo.toml` | A: feature `copy-volume` deleted |
| `docs/runs/2026-10-12/scripts/{s3_seq.sh,law_ab.sh}` | new: sequential sweep pair, alternating law timing |
| `docs/tier-cycle.md`, `docs/runs/2026-10-12/README.md`, `docs/learned-vs-fixed.md` if a row changes | results |
| the spec and this plan | results, departures. Both are git-excluded, so they exist only in the main checkout: edit them there, never commit them |

## Port rules (Phase A; Phase B keeps every rule's result)

Worked examples come from today's code at fd70bb7.

- **R1, reading.** `match e { Expr::App(f, a) => .. }` and `match &**x { .. }` become `match s.node(e) { Node::App(f, a)
  => .. }` inside the kernel, or `match e.node() { .. }` outside it. The children come out as owned `Expr`. In Phase A
  that is a refcount bump per child (part of A's informational cost); in B, a copy. `if let Expr::Var(k) = &**x`
  becomes `if let Node::Var(k) = s.node(x)`.
- **R2, building.** `Expr::App(f, a)` built raw becomes `app(f, a)`, and likewise for every former that has a named
  constructor (`var`, `sort`, `pi`, `lam`, `app`, `id`, `refl`, `jelim`, `wty`, `sup`, `wrec`, `sigma`, `pair`,
  `sigrec`). `Expr::Const(l)` and `Expr::Free(l)` become `mk(Node::Const(l))` and `mk(Node::Free(l))`. `Rc::new(e)`,
  `hc::intern_new(e)` and `hc::intern(e, ..)` on a built `e` become `e`, since it is a node already.
- **R3, types.** `Rc<Expr>` becomes `Expr`, `&Rc<Expr>` becomes `&Expr`, `(**a).clone()` and `(*a).clone()` become
  `a.clone()`, and `&**x` becomes `x`. Phase B's `clippy --fix` turns the `.clone()`s on the now-`Copy` `Expr` into
  copies.
- **R4, ranges.** `loose_of(e)` and `x.loose()` become `s.loose(e)` inside the kernel and `e.loose()` outside it;
  likewise `free`.
- **R5, identity.** `Rc::ptr_eq(a, b)` becomes `s.same(a, b)` inside the kernel. Outside it, it becomes
  `kernel::node_key(a) == kernel::node_key(b)` (tests only). `std::ptr::eq(a, b)` on `&Expr` becomes `s.same(a, b)`.
- **R6, pointer keys.** `PtrKey(x.clone())`, `Rc::as_ptr(x) as usize` (in a map that outlives the walk) and
  `*const Expr` keys become `s.key(x)`, of type `Key`; a value read back from a key is `s.from_key(&k)`. A key that
  only lives during a walk of a term held by its root (`bin::write`, `term_sizes`, `exceeds`, `canon`'s memo, the
  tests' node counters) may use `node_key(x)` (a `u64`). `hc`'s Phase A memos (`inst`, `shifts`, `whnf`, `hnf`,
  `bounds`, `arg_sets`) keep their `usize` addresses and `pin` until B2 replaces them.
- **R7, counts.** `Rc::strong_count(x) == 1` becomes `!s.shared(x)`, and `> 1` becomes `s.shared(x)` (departure 3).
- **R8, the context.** A kernel-internal function gets `s: &Spaces` as its first parameter. A public entry calls
  `with_spaces(|s| ..)` once. An internal call to a public entry (`whnf`, `def_eq`, `nf`, `instantiate`, `shift`)
  becomes the internal function with `s`.
- **R9, structure walks.** A `match` that rebuilds every variant with a per-child function becomes `n.map_kids(|c,
  under| ..)`. A `match` that visits every child becomes `n.for_kids(|c, under| ..)`. `under` is true exactly for a
  binder child: the second field of `Pi`/`Lam`/`W`/`Sigma`, `WRec`'s `children_ty`, and `Pair`'s `fam`.

Example, R1+R2+R4+R8+R9, `shift_unchecked`/`shift_via`/`shift_sigma_family` (kernel.rs:848-928) become one function:

```rust
fn shift_unchecked(s: &Spaces, e: &Expr, cutoff: u32, amount: i32) -> Expr {
    walk_count(1);
    grow(|| match s.node(e) {
        Node::Var(k) if k >= cutoff => var((k as i32 + amount) as u32),
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => e.clone(),
        n => s.mk(n.map_kids(|x, under| shift_child(s, &x, cutoff + under as u32, amount))),
    })
}
```

Example, `inst_rec` (kernel.rs:1656-1744), with the record-defeq probe block in the `Var` arm kept as it is:

```rust
fn inst_rec(s: &Spaces, e: &Expr, args: &[&Expr], aid: Option<Aid>, d: u32) -> Expr {
    walk_count(0);
    let m = args.len() as u32;
    let go = |x: Expr, under: bool| {
        let d = d + under as u32;
        if s.loose(&x) <= d {
            return x;
        }
        if aid.is_some() && s.loose(&x) != u32::MAX && !hc::uses(s, &x, d, m) {
            return shift_child(s, &x, d + m, -(m as i32));
        }
        let memo = !hc::low(s, &x);
        if memo && let Some(r) = hc::inst_get(s, &x, aid, d) {
            return r;
        }
        let r = inst_rec(s, &x, args, aid, d);
        if memo {
            hc::inst_put(s, &x, aid, d, &r);
        }
        r
    };
    grow(|| match s.node(e) {
        Node::Var(k) if k >= d + m => var(k - m),
        Node::Var(k) if k >= d => {
            let arg = args[(m - 1 - (k - d)) as usize];
            // (probe slots 5-16 as today)
            shift_in(s, arg, 0, d as i32)
        }
        Node::Var(_) | Node::Sort(_) | Node::Const(_) | Node::Free(_) => e.clone(),
        n => s.mk(n.map_kids(&go)),
    })
}
```

Here `shift_in(s, e, cutoff, amount)` is `shift`'s body with `s` (R8), and public `shift` is
`with_spaces(|s| shift_in(s, e, cutoff, amount))`. `Aid` is `u64` in Phase A and `u32` in B. `hc::args_id` returns
`Option<Aid>` in both phases (`None` where today returns 0).

Example, R6+R7, `infer_rc` (kernel.rs:2795):

```rust
if !s.shared(e) {
    walk_count(18);
    return infer_node(s, g, ic, ctx, cid, e);
}
let key = (s.key(e), ic.memo_context(s, cid, e));
if let Some(ty) = ic.types.get(&key) {
    walk_count(19);
    return Ok(s.from_key(ty));
}
walk_count(20);
let ty = infer_node(s, g, ic, ctx, cid, e)?;
ic.types.insert(key, s.key(&ty));
Ok(ty)
```

---

### Task 0: worktree and baseline

**Files:** none changed.

- [ ] **Step 1:** Make the worktree, then record the baseline counts and clippy's warnings:

```bash
cd "/c/Users/Winston Li/Documents/GitHub/tatic" && git worktree add ../tatic-s3 -b id-arena-stage3 fd70bb7
cd ../tatic-s3 && CARGO_TARGET_DIR=target/s3 cargo test --release -j 8 2>&1 | grep -E "^test result|Running" > "$(cygpath -u "$TEMP")/s3_base_counts.txt"
CARGO_TARGET_DIR=target/s3 cargo clippy --all-targets -j 8 2>&1 | grep -cE "^warning" > "$(cygpath -u "$TEMP")/s3_base_clippy.txt"
```

  Expected: about 10-15 minutes (a cold build), and every `test result` line `ok`. If one fails, stop: the baseline is
  broken.

### Task 1: the law-time harness and the base exes

**Files:**
- Modify: `tests/church_bv/rewrite.rs` (append `law_time`)
- Create: `docs/runs/2026-10-12/scripts/law_ab.sh`, `docs/runs/2026-10-12/scripts/s3_seq.sh`

**Interfaces:** produces `rewrite::law_time` (env `LAW_RULE` default 33, `LAW_N` default 8, `LAW_REPS` default 5;
prints `LAWT rule=.. n=.. reps=.. min=.. med=..`), and the base exes `$TEMP/bv_s3_base.exe` and
`$TEMP/proofs_s3_base.exe`.

- [ ] **Step 1: The harness.** Append to `tests/church_bv/rewrite.rs`. It is the probe recovered from 2026-10-14
  (`law_time_probe`), now kept, with one region per rep:

```rust
/// Check time of one rule's law alone: rule `LAW_RULE` (default 33) of the cmp3d own-rules file at `LAW_N` bits
/// (default 8), `LAW_REPS` times (default 5) after one warm-up. Each rep builds the proof and checks it in its own
/// `scoped`, one region, and times only the check. Prints `LAWT rule=.. n=.. reps=.. min=.. med=..`. The id arena's
/// A/B harness (plan docs/superpowers/plans/2026-10-14-id-arena-stage3.md; `scripts/law_ab.sh`).
#[test]
#[ignore]
pub fn law_time() {
    let env = |k: &str, d: usize| std::env::var(k).map_or(d, |v| v.parse().unwrap());
    let (i, n, reps) = (env("LAW_RULE", 33), env("LAW_N", 8), env("LAW_REPS", 5).max(1));
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/docs/runs/2026-10-12/scripts/cmp3d_own_rules.txt");
    let rules = parse_rules(&std::fs::read_to_string(path).unwrap());
    let (l, r) = &rules[i];
    let k = l.max_var().max(r.max_var()) + 1;
    let once = || {
        tatic::kernel::scoped(|| {
            let (lp, ls) = prove_rule(n, k, l, r).expect("the rule proves");
            let (p, lemmas) = PARAMS.with(|c| c.borrow_mut().take()).unwrap_or_else(|| (Postulates::new(), Vec::new()));
            let t = Instant::now();
            let ok = p.check_open(&lp, &ls);
            let took = t.elapsed();
            PARAMS.with(|c| *c.borrow_mut() = Some((p, lemmas)));
            ok.expect("the law checks");
            took
        })
    };
    once();
    let mut ts: Vec<_> = (0..reps).map(|_| once()).collect();
    ts.sort();
    println!("LAWT rule={i} n={n} reps={reps} min={:?} med={:?}", ts[0], ts[reps / 2]);
}
```

- [ ] **Step 2: The scripts.** `law_ab.sh`:

```bash
# law_ab.sh <old exe> <new exe> <pairs> <n>...: rule 33's law check time (church_bv `rewrite::law_time`), old and new
# alternating (old first on odd pairs), each run pinned to 12 cores at BelowNormal; LAW_REPS (default 5) reps per run.
# Appends "<tag> LAWT ..." lines to $TEMP/kk/law_ab.txt, then "ALL". Id arena Stage 3 (plan 2026-10-14-id-arena-stage3).
old=$1; new=$2; pairs=$3; shift 3
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; out=$k/law_ab.txt; : > $out
run() { LAW_N=$2 LAW_REPS=${LAW_REPS:-5} cmd //c start "" //b //belownormal //affinity FFF //wait "$1" rewrite::law_time --exact --ignored --nocapture > $k/law_run.txt 2>&1
  grep '^LAWT' $k/law_run.txt | sed "s/^/$3 /" >> $out; }
for n in "$@"; do for i in $(seq 1 $pairs); do
  if [ $((i % 2)) = 1 ]; then run "$old" $n old; run "$new" $n new; else run "$new" $n new; run "$old" $n old; fi
done; done
echo ALL >> $out
```

  `s3_seq.sh` (Stage 2's `stage2_seq.sh` with the exes and tag as arguments, and no `cv` run):

```bash
# usage: s3_seq.sh <tag> <old exe> <new exe>: id arena Stage 3, one sweep at a time (SWEEP="mines own pooled"), order new,
# old on salt 1 and old, new on salt 2, into $TEMP/kk/<tag>_{old,new}_{1,2}; "<tag> ALL" in $TEMP/kk/s3_done.txt at the end.
tag=$1; old=$2; new=$3
k=$(cygpath -u "$TEMP")/kk; mkdir -p $k; touch $k/s3_done.txt; sed -i "/^$tag /d" $k/s3_done.txt
run() { exe=$1; arm=$2; salt=$3; out=$k/${tag}_${arm}_$salt; rm -rf $out; mkdir -p $out; s=$(date +%s)
  MACHINE_STATE=0 SWEEP_OUT=$out SALT=$salt SWEEP="mines own pooled" cmd //c start "" //b //belownormal //affinity FFF //wait "$exe" driver::sweep --exact --ignored --nocapture > $out/log.txt 2>&1
  echo "$tag $arm $salt $(( $(date +%s) - s ))s" >> $k/s3_done.txt; }
run "$new" new 1; run "$old" old 1; run "$old" old 2; run "$new" new 2
echo "$tag ALL" >> $k/s3_done.txt
```

- [ ] **Step 3: Build, spike and copy the base exes.**
  - `CARGO_TARGET_DIR=target/s3 cargo test --release -j 8 --test church_bv --no-run`; copy the printed `Executable`
    path to `$TEMP/bv_s3_base.exe`.
  - `CARGO_TARGET_DIR=target/s3 cargo bench --bench proofs -j 8 --no-run`; copy its executable to
    `$TEMP/proofs_s3_base.exe`.
  - Spike the harness's duration with one run each at n=8 and n=64, `LAW_REPS=3`, pinned as in `law_ab.sh`. Record
    both wall times in this plan's Task 6 step for the timing budget.
  - Expected: `LAWT` lines with `ok` checks. If the warm-up `expect` fails, the rule index or file path is wrong: stop.

- [ ] **Step 4: Commit** ("church_bv: law_time, rule 33's law check time per region (id arena Stage 3 harness); scripts
  law_ab.sh and s3_seq.sh"). Then re-record `$TEMP/s3_base_counts.txt` at this commit with Task 0's command, since
  church_bv now has one more ignored test. Every later count compares against this one.

### Task 2 (A2): the handle API on `Rc` storage

**Files:** everything in the file map marked A. This is one atomic switch: nothing between its first edit and Step 8
compiles all targets. The steps are ordered so each compile gate covers a growing set.

**Interfaces (produced, used by everything after):**
- `pub enum Node<C>` with `for_kids`, `map_kids`, `tag_leaf`, `same_shape` and `ranges` (code below).
- `pub struct Expr`, with `node()`, `loose()`, `free()` and `shared()`; `pub fn mk(Node<Expr>) -> Expr`; and
  `pub fn node_key(&Expr) -> u64`.
- `pub(crate) struct Spaces`, `pub(crate) fn with_spaces`, `pub(crate) type Key` and `pub(crate) type Aid`, with
  `Spaces::{node, mk, loose, free, shared, same, key, from_key, uses_slot, set_uses_slot}`.
- The record-defeq probe `pub fn take_built() -> (u64, u64)`.

- [ ] **Step 1: `Node<C>`.** Replace `pub enum Expr` (kernel.rs:363-464) with this. Every variant doc carries over
  verbatim from today's `Expr`, and so does the `Rc`-not-`Box` rationale, retold for the handle:

```rust
/// A term's outermost constructor over children of type `C`. `Node<Expr>` is what [`Expr::node`] hands out, and the
/// arena stores `Node<Ref>`. (Variant docs as today's `Expr`'s.)
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Node<C> {
    Var(u32),
    Sort(u32),
    Const(u32),
    Free(u32),
    Pi(C, C),
    Lam(C, C),
    App(C, C),
    Id(C, C, C),
    Refl(C),
    J { motive: C, base: C, a: C, b: C, p: C },
    W(C, C),
    Sup(C, C),
    WRec { motive: C, children_ty: C, step: C, target: C },
    Sigma(C, C),
    Pair(C, C, C),
    SigRec { motive: C, step: C, target: C },
}

impl<C> Node<C> {
    /// Calls `f` on each child in field order, with whether the child sits under a binder of this node (the second
    /// field of `Pi`/`Lam`/`W`/`Sigma`, `WRec`'s `children_ty`, `Pair`'s `fam`).
    #[inline(always)]
    pub fn for_kids<'a>(&'a self, mut f: impl FnMut(&'a C, bool)) {
        use Node::*;
        match self {
            Var(_) | Sort(_) | Const(_) | Free(_) => {}
            Refl(a) => f(a, false),
            Pi(a, b) | Lam(a, b) | W(a, b) | Sigma(a, b) => {
                f(a, false);
                f(b, true);
            }
            App(a, b) | Sup(a, b) => {
                f(a, false);
                f(b, false);
            }
            Id(a, b, c) | SigRec { motive: a, step: b, target: c } => {
                f(a, false);
                f(b, false);
                f(c, false);
            }
            Pair(fam, a, b) => {
                f(fam, true);
                f(a, false);
                f(b, false);
            }
            J { motive, base, a, b, p } => {
                for c in [motive, base, a, b, p] {
                    f(c, false);
                }
            }
            WRec { motive, children_ty, step, target } => {
                f(motive, false);
                f(children_ty, true);
                f(step, false);
                f(target, false);
            }
        }
    }

    /// The same constructor with each child replaced by `f(child, under_binder)`, called in field order.
    #[inline(always)]
    pub fn map_kids<D>(self, mut f: impl FnMut(C, bool) -> D) -> Node<D> {
        use Node::*;
        match self {
            Var(k) => Var(k),
            Sort(k) => Sort(k),
            Const(k) => Const(k),
            Free(k) => Free(k),
            Pi(a, b) => Pi(f(a, false), f(b, true)),
            Lam(a, b) => Lam(f(a, false), f(b, true)),
            App(a, b) => App(f(a, false), f(b, false)),
            Id(a, b, c) => Id(f(a, false), f(b, false), f(c, false)),
            Refl(a) => Refl(f(a, false)),
            J { motive, base, a, b, p } => J { motive: f(motive, false), base: f(base, false), a: f(a, false), b: f(b, false), p: f(p, false) },
            W(a, b) => W(f(a, false), f(b, true)),
            Sup(a, b) => Sup(f(a, false), f(b, false)),
            WRec { motive, children_ty, step, target } => {
                WRec { motive: f(motive, false), children_ty: f(children_ty, true), step: f(step, false), target: f(target, false) }
            }
            Sigma(a, b) => Sigma(f(a, false), f(b, true)),
            Pair(fam, a, b) => Pair(f(fam, true), f(a, false), f(b, false)),
            SigRec { motive, step, target } => SigRec { motive: f(motive, false), step: f(step, false), target: f(target, false) },
        }
    }

    /// The constructor's tag and leaf value, as the node tables key them.
    pub fn tag_leaf(&self) -> (u8, u32) {
        use Node::*;
        match self {
            Var(k) => (0, *k),
            Sort(k) => (1, *k),
            Const(k) => (2, *k),
            Free(k) => (3, *k),
            Pi(..) => (4, 0),
            Lam(..) => (5, 0),
            App(..) => (6, 0),
            Id(..) => (7, 0),
            Refl(..) => (8, 0),
            J { .. } => (9, 0),
            W(..) => (10, 0),
            Sup(..) => (11, 0),
            WRec { .. } => (12, 0),
            Sigma(..) => (13, 0),
            Pair(..) => (14, 0),
            SigRec { .. } => (15, 0),
        }
    }

    /// Whether the two have the same constructor (and leaf value) and `c` holds of each pair of children in field
    /// order, stopping at the first that fails. Syntactic equality and `conv_whnf` are both this with a different `c`.
    pub fn same_shape(&self, other: &Node<C>, mut c: impl FnMut(&C, &C) -> bool) -> bool {
        if self.tag_leaf() != other.tag_leaf() {
            return false;
        }
        let mut kids: [Option<&C>; 5] = [None; 5];
        let mut i = 0;
        other.for_kids(|k, _| {
            kids[i] = Some(k);
            i += 1;
        });
        let (mut ok, mut j) = (true, 0);
        self.for_kids(|k, _| {
            ok = ok && c(k, kids[j].unwrap());
            j += 1;
        });
        ok
    }

    /// One more than the largest loose `Var` index and one more than the largest `Free` level, from the children's
    /// (`loose`, `free`): a binder child has one loose variable fewer out here. Saturating, so `Var(u32::MAX)` doesn't
    /// wrap to "closed" (exact only below `u32::MAX`, which no real term reaches).
    pub fn ranges(&self, loose: impl Fn(&C) -> u32, free: impl Fn(&C) -> u32) -> (u32, u32) {
        match self {
            Node::Var(k) => (k.saturating_add(1), 0),
            Node::Free(l) => (0, l.saturating_add(1)),
            _ => {
                let (mut l, mut f) = (0, 0);
                self.for_kids(|c, under| {
                    l = l.max(if under { loose(c).saturating_sub(1) } else { loose(c) });
                    f = f.max(free(c));
                });
                (l, f)
            }
        }
    }
}
```

  `same_shape` through `for_kids` stops calling `c` after the first false (`ok && ..`), so the visit cost matches
  today's. Keep today's `same_shape` doc text on it.

- [ ] **Step 2: `Expr`, `Header`, the stub, `mk`.** Replace `pub struct Rc<T>`/`struct Node<T>` and their impls
  (kernel.rs:51-195) and `loose_of`/`free_of` (204-241) with:

```rust
/// A term: a handle to its outermost node. Cloning is a refcount bump; the node holds its children as `Expr`s, so a
/// term is a DAG and every subterm a node (this replaces today's root `Expr` over `Rc<Expr>` children). The id arena
/// (spec docs/superpowers/specs/2026-10-14-id-arena-spec.md) replaces the `Rc` with an id behind the same API.
#[derive(Clone)]
pub struct Expr(std::rc::Rc<Header>);

struct Header {
    loose: u32,
    free: u32,
    /// The `hc` table generation this node is canonical in (0: not).
    generation: std::cell::Cell<u32>,
    /// The last [`hc::uses`] answer for this node, packed by [`Spaces::uses_slot`] (0: none).
    uses: std::cell::Cell<u32>,
    /// Nodes built over this one, saturating at 2 ([`Spaces::shared`]).
    parents: std::cell::Cell<u8>,
    node: Node<Expr>,
}

impl Expr {
    /// A new node over `n`, outside any table ([`hc::intern`] decides whether to share one instead).
    fn build(n: Node<Expr>) -> Expr {
        let (loose, free) = n.ranges(|c| c.0.loose, |c| c.0.free);
        n.for_kids(|c, _| c.0.parents.set(c.0.parents.get().saturating_add(1).min(2)));
        Expr(std::rc::Rc::new(Header {
            loose,
            free,
            generation: std::cell::Cell::new(0),
            uses: std::cell::Cell::new(0),
            parents: std::cell::Cell::new(0),
            node: n,
        }))
    }

    /// Whether this node and everything under it came from the current `hc` table, so that two canonical nodes are
    /// structurally equal exactly when they are the same node. False outside a scope.
    #[inline(always)]
    fn canonical(&self) -> bool {
        let g = self.0.generation.get();
        g != 0 && g == hc::generation()
    }

    /// The outermost constructor, over the children.
    pub fn node(&self) -> Node<Expr> {
        with_spaces(|s| s.node(self))
    }
    /// One more than the largest loose `Var` index, 0 when closed (saturating at `u32::MAX`).
    pub fn loose(&self) -> u32 {
        with_spaces(|s| s.loose(self))
    }
    /// One more than the largest `Free` level, 0 when there is none (saturating).
    pub fn free(&self) -> u32 {
        with_spaces(|s| s.free(self))
    }
    /// Whether two or more nodes are built over this one (the memos' "worth remembering" test).
    pub fn shared(&self) -> bool {
        with_spaces(|s| s.shared(self))
    }
}

/// The node `n`, interned while a scope's table is on.
pub fn mk(n: Node<Expr>) -> Expr {
    with_spaces(|s| s.mk(n))
}

/// An id for `e`'s node: two handles have the same key exactly when they name the same node. For tests, and for maps
/// that live only while a root keeps the nodes they key alive (`bin::write`, `term_sizes`, `kernel_lazy`).
pub fn node_key(e: &Expr) -> u64 {
    std::rc::Rc::as_ptr(&e.0) as u64
}

/// The kernel's view of term storage. A stub over `Rc` nodes until the id arena (Phase B) gives it state; internals
/// take it as `s` so the arena changes only this type.
pub(crate) struct Spaces;

/// Runs `f` with this thread's spaces.
#[inline(always)]
pub(crate) fn with_spaces<R>(f: impl FnOnce(&Spaces) -> R) -> R {
    f(&Spaces)
}

/// A map key naming a node. It holds the node, so no address is reused while the map lives.
pub(crate) type Key = PtrKey;
/// An argument list's id in the instantiation memo ([`hc::args_id`]).
pub(crate) type Aid = u64;

impl Spaces {
    #[inline(always)]
    pub(crate) fn node(&self, e: &Expr) -> Node<Expr> {
        e.0.node.clone()
    }
    #[inline(always)]
    pub(crate) fn mk(&self, n: Node<Expr>) -> Expr {
        hc::intern(n)
    }
    #[inline(always)]
    pub(crate) fn loose(&self, e: &Expr) -> u32 {
        e.0.loose
    }
    #[inline(always)]
    pub(crate) fn free(&self, e: &Expr) -> u32 {
        e.0.free
    }
    #[inline(always)]
    pub(crate) fn shared(&self, e: &Expr) -> bool {
        e.0.parents.get() > 1
    }
    #[inline(always)]
    pub(crate) fn same(&self, a: &Expr, b: &Expr) -> bool {
        std::rc::Rc::ptr_eq(&a.0, &b.0)
    }
    #[inline(always)]
    pub(crate) fn key(&self, e: &Expr) -> Key {
        PtrKey(e.clone())
    }
    #[inline(always)]
    pub(crate) fn from_key(&self, k: &Key) -> Expr {
        k.0.clone()
    }
    /// The node's remembered `uses(e, d, m)`, if the slot holds that query. The slot packs a set bit, `d` and `m` in 15
    /// bits each, and the answer; queries that don't fit are never stored.
    #[inline(always)]
    pub(crate) fn uses_slot(&self, e: &Expr, d: u32, m: u32) -> Option<bool> {
        let s = e.0.uses.get();
        (d < 1 << 15 && m < 1 << 15 && s >> 1 == (1 << 30 | d << 15 | m)).then_some(s & 1 == 1)
    }
    #[inline(always)]
    pub(crate) fn set_uses_slot(&self, e: &Expr, d: u32, m: u32, r: bool) {
        if d < 1 << 15 && m < 1 << 15 {
            e.0.uses.set((1 << 30 | d << 15 | m) << 1 | r as u32);
        }
    }
}
```

  `PtrKey` becomes `#[derive(Clone)] pub(crate) struct PtrKey(Expr)`, hashing `node_key` (`InferCache.info`'s
  `Option<Key>` is cloned). Then:
  - **`PartialEq for Expr`:** `Rc::ptr_eq(&self.0, &other.0) || (!(self.canonical() && other.canonical()) &&
    grow(|| self.0.node.same_shape(&other.0.node, |p, q| p == q)))`. That is today's semantics, with one level per
    recursion.
  - **`Drop`:** `impl Drop for Header`. If `!stack_ok()`, it moves `self.node` out with `std::mem::replace(&mut
    self.node, Node::Sort(0))` and drops it inside `grow_slow`. `LEAF` and `Drop for Expr` are deleted. A shared child
    only loses a reference, so moving the whole node is as safe as today's per-child swap and needs no thread-local.
  - **`Debug`:** `write_expr` takes `&Node<Expr>` and a child printer over `&Expr`, and `Debug for Expr` is
    `write_expr(&self.node(), f, &|c, f| fmt::Debug::fmt(c, f))`.
  - **Constructors:** each named constructor is `mk(Node::X(..))`. `var` and `sort` too: they intern now, where today
    they built leaves outside the table. `app2`, `app3` and `arrow` are unchanged.
  - **Deleted:**
    - `Rc::new`, `with_ranges`, `canon()` (the `record-defeq` field), `as_ptr`, `strong_count` and `AsRef`/`Deref`;
    - `hc_probe` (the file, its `mod`, `pub use` and every `_hc_guard` line);
    - `copy_volume` (the module, `copy_volume_thread`/`_process`, `CopyVolume`, the `region`/`pid` fields, its
      `Scope::enter`/`drop` hooks and `persist`'s call) and the `copy-volume` feature in `Cargo.toml`;
    - `instantiate_memo`, `rename_context_to_frees` and `rename_pair_memo`.
  - **Added, with `record-defeq`:** `take_built() -> (u64, u64)`, the counts of `hc::intern` calls and new nodes since
    the last call (thread-local `Cell`s bumped in `hc::intern_as`).

- [ ] **Step 3: `hc` on `Node`.**
  - `hc::intern(n: Node<Expr>) -> Expr` is `intern_as(n, Expr::build)`. `intern_as`, `key_of(&Node<Expr>)` and the
    table's `nodes: HashTable<(u64, Expr)>` keep their logic, with `key_of` reading `n.tag_leaf()` and
    `node_key` of each child.
  - `intern_new` and the `for_kids`/`tag_leaf`/`map_kids`/`under_binder` copies inside `hc` are deleted; their callers
    use `Node`'s methods.
  - `canon(x, memo)` keeps `x` itself when no child changed: `let n = grow(|| s.node(x).map_kids(|c, _| canon(s, &c,
    memo))); if n.same_shape(&x.0.node, |p, q| s.same(p, q)) { intern_as(n, |_| x.clone()) } else { intern(n) }`.
  - `canonical_inputs` returns `(canon(e), canon(expected))` when it interns, and the inputs as they are otherwise.
    So `check_in`'s two `hc::intern(.., None)` calls on the roots go, since `canon` handles a root as any node.
  - `uses` and `lowest_loose` walk with `s.node(x).for_kids(|c, under| ..)`. `args_id` returns `Option<Aid>`, with
    `None` where it returned 0, and its argument id interns with `intern(s.node(a))` as today's
    `intern((***a).clone(), None)` does.
  - Memo accessors take `aid: Option<Aid>`. The `keep`/`pin`/`WARM_UP`/`CALLS`/`activate`/`Scope` machinery is
    unchanged in Phase A.

- [ ] **Step 4: Port the rest of `kernel.rs`** by R1-R9, function by function in file order, with these merges and
  deletions:
  - **`shift`:** `shift_via` and `shift_sigma_family` fold into `shift_unchecked` (example above), with `shift_in` as
    the internal entry.
  - **Instantiation:** `instantiate`, `instantiate_n` and `subst_top` take `s`. `inst_rec` is as in the example.
  - **`is_var_free`:** `s.loose(e) <= idx` returns false, a `Var` compares, and anything else is `let mut f = false;
    s.node(e).for_kids(|c, under| f = f || is_var_free(s, c, idx + under as u32)); f`, inside `grow`.
  - **`whnf`:** `whnf_impl` and `whnf_rc` merge into `whnf_in(s, e, cache) -> Expr`, which is `whnf_rc`'s body: the
    table memo while the table is on, `cache.whnf` otherwise.
    - `whnf_step(s, e, cache) -> Option<Expr>` keeps its arms. Every former `Rc::new(Expr::App(x, y))` is `app(x,
      y)`, and `Rc::ptr_eq(&wf, f)` is `s.same(&wf, &f)`.
    - Public `whnf` is `with_spaces(|s| whnf_in(s, e, &mut ReductionCache::default()))`.
  - **`nf`:** `nf_impl` and `nf_rc` merge into `nf_in(s, e, cache)`: the `cache.nf` lookup, then `nf_whnf(s,
    &whnf_in(..))`. `nf_whnf` is `match s.node(w) { leaf => w.clone(), n => s.mk(n.map_kids(|c, _| nf_in(s, &c,
    cache))) }`, and `nf_sigma_family` is deleted.
  - **`hnf`:** `hnf_rc` and `under_lams` take `s`. Their `Rc::new(..)` become constructor calls.
  - **`conv`:** `conv` and `conv_rc` merge into `conv(s, a, b, cache)`:

```rust
fn conv(s: &Spaces, a: &Expr, b: &Expr, cache: &mut ReductionCache) -> bool {
    if s.same(a, b) {
        return true;
    }
    let noted = cache.unequal.contains(&(s.key(a), s.key(b)));
    if !noted && eq_noting(s, a, b, &mut cache.unequal) {
        return true;
    }
    conv_whnf(s, &whnf_in(s, a, cache), &whnf_in(s, b, cache), cache)
}
```

  - **`def_eq`:** public `def_eq` is `hc::scoped(false, || with_spaces(|s| def_eq_in(s, a, b)))`. `def_eq_in(s, a, b)`
    holds today's record-defeq lines (`site(3)`, the `SEEN` clear) and `conv(s, a, b, &mut
    ReductionCache::default())`. Internal callers (`infer_sup`, `WRec`, `check_rc`) call `def_eq_in`.
  - **Expectations:** `expect_sort`, `expect_pi`, `expect_w` and `expect_sigma` take `s` and call `whnf_in(s, e, &mut
    ReductionCache::default())`, as today's call to public `whnf` makes a fresh cache. `check_rc`'s
    `whnf(expected)` does the same.
  - **`brief_nf`:** `Nf(Expr, &RefCell<ReductionCache>)`, with the node read through `with_spaces`.
  - **`InferCache`:**
    - `types: PtrMap<(Key, (u32, u32)), Key>`, `contexts: PtrMap<(u32, Key), u32>`, `lows: PtrMap<(Key, u32), u32>`;
    - `info: Vec<(u32, Option<Key>, u32)>` (`None` for `fresh`), and `windows: PtrMap<(u32, Key), u32>` keyed by
      `info[c].1.clone().expect("a window binder has a type")` (the walk stops at a `fresh` binder before reading
      it);
    - `enter`, `memo_context` and `window` take `s`;
    - the probe `relevant_signature` keys by `node_key`, and reads `info` entries by reference (`let (l, t, w) =
      &ic.info[c]`), since `Key` isn't `Copy` in Phase A.
  - **Typing:** `infer_node`, `check_rc` and the `infer_*` helpers take `s`, by R1-R8. `check_in` and `infer_in` call
    them through `with_spaces`. `infer_in` passes `e` itself (it is a node now).
  - **Probes:** `term_sizes` walks with `for_kids`, memoised by `node_key`. The record-defeq `SEEN` is keyed by
    `(node_key(arg), d)`. `DEFEQ_LOG` keeps `(PExpr, PExpr, u32)`: `persist` at the push, and `take_defeq_log` maps
    back with `.get()`.

  **Compile gate 1:** `CARGO_TARGET_DIR=target/s3 cargo build --lib -j 8` (errors in `postulates.rs`, `bin.rs` and
  `kernel_lazy.rs` are expected until Step 5). Work until `kernel.rs` itself reports none.

- [ ] **Step 5: `postulates.rs`, `bin.rs`, `kernel_lazy.rs`, `proof/instance.rs`.**
  - **`postulates.rs`:**
    - `FreesMemo` is `HashMap<(Key, u32), Expr>`.
    - `abstract_frees_in(s, e, first, levels, d, memo)` is: `if s.free(e) <= first { return e.clone() }`; then
      `match s.node(e)`, where `Free(l)` maps to its `Var` or itself and every other leaf is `e.clone()`, and the
      rest is `s.mk(n.map_kids(|x, under| go(x, d + under as u32)))`.
    - `go` skips the memo when `!s.shared(&x)` (R7).
    - The public methods reach `s` through `with_spaces`.
    - `get(pos)` is `mk(Node::Const(pos as u32))` and `bind`'s `Expr::Free(l)` is `mk(Node::Free(l))`.
  - **`bin.rs`:** `children` becomes `for_kids` into a `Vec<Expr>`, and `tag` is a match on `node()`. `write`'s index
    is `HashMap<u64, u64>` by `node_key`, with the stack holding `Expr` handles. `read` is unchanged (it uses
    constructors).
  - **`kernel_lazy.rs`:**
    - `KRc<Expr>` becomes `Expr` and `&**e` becomes `e.node()` (R1).
    - `record`'s `strong_count` histogram has two buckets, `shared()` false or true. The `by_count` arrays keep their
      size, and the one reader (`encoding.rs` `replay_defeq_queries`, record-defeq) prints them as before.
    - `memo_key` uses `node_key(e)`, and `memo_on` uses `e.shared()`.
    - Its tests' `KRc::new(Expr::Sup(..))` becomes `sup(..)`.
  - **`proof/instance.rs`** (one site, :1339): R1.

  **Compile gate 2:** `cargo build --lib -j 8` clean, and `cargo build --lib -j 8 --features record-defeq` clean.

- [ ] **Step 6: `kernel/tests.rs` and `proof/tests.rs`** by R1-R9. Then:
  - **Deleted, `a_node_is_64_bytes`:** the sizes change twice in this plan. B1 asserts the stored node's 24 B.
  - **Deleted, `copy_volume_counts_each_region_node_once`:** the feature is gone. It is `cfg(feature =
    "copy-volume")`, so the default count doesn't include it.
  - **Changed, `uses_slot_is_free_and_agrees_with_the_walk`:** it loses its first line (the size assert) and its
    `cfg(not(...))`. Every other test is ported unchanged in what it asserts.
  - **Ported, `infer_memo_changes_no_answer`:** its helper `shares_nothing` walks with `for_kids` and tests
    `!c.shared()` in place of `strong_count(c) == 1`. The pool becomes `Vec<Expr>` built with the constructors.
    (Phase B deletes it, Task 5.)
  - **`ptr_eq` sites:** `Rc::ptr_eq(x, y)` becomes `node_key(x) == node_key(y)`.
  - **`proof/tests.rs`:** `dag_size` is deleted for `kernel::term_sizes(e).0`, which counts the same thing.
  - **`dropping_a_deep_term_does_not_overflow_the_stack`** stays. It now guards `Drop for Header`.

  **Compile gate 3:** `CARGO_TARGET_DIR=target/s3 cargo test --lib --release -j 8`. All pass, and the count is the
  baseline's lib count minus one (`a_node_is_64_bytes`).

- [ ] **Step 7: Integration tests and benches** (there is no `examples/` directory).
  - **Pattern sites:** R1-R9 in `tests/church_bv/{search,machine,encoding,rewrite,lemma_cache}.rs`,
    `tests/proof_scope.rs`, `tests/kernel_fuzz.rs`, `tests/kernel_soundness_fuzz.rs` (its `count_nodes`,
    `nth_subterm` and `replace` on `for_kids`/`map_kids`) and `benches/*.rs`.
    `lemma_cache.rs`'s `loose_of(stmt)` becomes `stmt.loose()`.
  - **Name clash:** `encoding.rs`'s `pub fn mk(args: &[Expr])` (the Church tuple, :353) collides with the new
    `kernel::mk`, since `main.rs` glob-imports both. Rename it `church_tuple` at its definition and its 8 call sites
    (`grep -nw "mk(" tests/church_bv/*.rs`).
  - **`encoding.rs`:**
    - the `Rc::ptr_eq` asserts (265-292) become `node_key` equality;
    - `intern_lookup_vs_rc_new` is **deleted**: it timed `kernel::Rc` against a map for a design question doc section
      59 settled, and `kernel::Rc` is gone;
    - the `take_hc_built`/`take_hc_inst` printout in `walk_counts_on_hard_queries` becomes one `take_built()` line;
    - the `rename_pair_memo` block (957-972) is deleted.
  - **`search.rs`:** the three `COPYVOL` printlns and their `cfg` are deleted, and `take_hc_built` becomes
    `take_built` (2121-2149).

  **Compile gate 4:** `CARGO_TARGET_DIR=target/s3 cargo build --release --all-targets -j 8` and the same with
  `--features record-defeq`, both clean. Then `cargo clippy --all-targets -j 8`: no more warnings than
  `$TEMP/s3_base_clippy.txt`.

- [ ] **Step 8: Full suite.** `CARGO_TARGET_DIR=target/s3 cargo test --release -j 8 2>&1 | grep -E "^test
  result|Running" > $TEMP/s3_a_counts.txt`, then diff it against `s3_base_counts.txt`. Expected: the same per-binary
  counts except lib (-1, `a_node_is_64_bytes`) and church_bv ignored (-1, `intern_lookup_vs_rc_new`; the baseline
  already includes Task 1's `law_time`). Any other difference stops the task.

- [ ] **Step 9: Commit** ("kernel: terms are nodes behind a handle (id arena Stage 3, Phase A)", listing the deletions,
  merges and tests deleted).

### Task 3 (A3): Phase A gates

- [ ] **Step 1: Exes.** Build church_bv at Task 2's commit (`--no-run`) and copy it to `$TEMP/bv_s3_a.exe`.
- [ ] **Step 2: Identical outputs.** Run `s3_seq.sh s3a $TEMP/bv_s3_base.exe $TEMP/bv_s3_a.exe` in the background,
  notified on `s3a ALL` in `s3_done.txt` (a loop that exits). Then compare:

```bash
k=$(cygpath -u "$TEMP")/kk; for s in 1 2; do echo "salt $s:"; diff -rq $k/s3a_old_$s $k/s3a_new_$s; done
```

  Expected: about 1.5 minutes for the four runs (Stage 2's took 18-22 s each). Every differing file must pass the
  Global Constraints' rule, checked with `diff <(sed -E 's/[0-9]+(\.[0-9]+)?(s|ms|µs)\b/T/g;
  s/s3a_(old|new)/RUN/g' a) <(same for b)`. The rule is the same as Phase B's. A
  can change a lemma cache's bytes, because it interns more than today (leaves, roots, and the former bypasses), and
  `bin::write` encodes whatever sharing the term has. The `LEMMA_CACHE` counts must still be equal, and the `.tsv`
  files identical. List each lemma-cache difference in the report.
- [ ] **Step 3: Timing (informational, no gate).** Report the load and RTP, then:
  - `cpu_ab.ps1 $TEMP\bv_s3_base.exe - 8 $TEMP\bv_s3_a.exe`;
  - `law_ab.sh $TEMP/bv_s3_base.exe $TEMP/bv_s3_a.exe 3 8 64` (with `LAW_REPS` sized from Task 1's spike, so n=64
    runs at least 5 reps).

  Expected cost: refcount bumps per `node()` read, the 96-byte block, and the merged memos' extra traffic. Record the
  numbers. A loss here is A's own and B removes most of it, so it does not stop the plan. A loss over 30% is still
  worth one profile before B, to know what B must recover.
- [ ] **Step 4:** Rows in `docs/runs/2026-10-12/README.md` (`s3a_*`, the timing). Commit them with the next docs
  commit (Task 6), not now.

### Task 4 (B1): `spaces.rs`, standalone

**Files:** Create `src/kernel/spaces.rs`. Modify `src/kernel.rs`: add `mod spaces;` only. Nothing uses it until Task 5,
so mark the module `#[allow(dead_code)]` until then, and Task 5 removes the allow.

**Interfaces (produced):** `Ref`, `LIST_BIT`, `Spaces::{new, epoch, resolve, live, node_at, build, loose_at, free_at,
parents_at, uses_at, set_uses_at, persist, open, close}`, `Spaces.memos: RefCell<Memos>`, `Memos`, `IdHasher`,
`IdMap`, `IdSet`.

- [ ] **Step 1: Write the file:**

```rust
//! The id arena (spec `docs/superpowers/specs/2026-10-14-id-arena-spec.md`, "Design"). A term is a 32-bit [`Ref`] into
//! one of two per-thread spaces, both hash-consed:
//! - the *persistent* space only grows;
//! - the *region* is a check's working memory, opened by the outermost `scoped` and freed in bulk when it closes.
//!
//! A persistent node has only persistent children. While a region is open, `persist` copies region nodes out bottom-up
//! and records each copy's region *twin*. Reading a persistent `Ref` at or above `w` (the persistent length when the
//! region opened) gives its twin. So no two `Ref`s that callers see name the same term (Invariant I), and `==` on
//! resolved `Ref`s is structural equality.
//!
//! The one `unsafe` contract is local to this file: `inner()`'s `&mut` lives within one method body, never across a
//! call that can reach `inner` again (`persist` drops it before recursing), and no method returns a reference into
//! the vectors. Reads return copies, so a vector that grows never leaves a borrow dangling.

use super::Node;
use std::cell::{RefCell, UnsafeCell};
use std::hash::BuildHasherDefault;

/// A node in one of the two spaces: bit 31 set for the region, bits 0-29 the index into that space.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct Ref(pub(crate) u32);

const REGION_BIT: u32 = 1 << 31;
const INDEX_MASK: u32 = (1 << 30) - 1;
/// Set in an argument-list id (`hc::args_id`) and clear in every `Ref`, so the two never collide as `Memos::inst` keys.
pub(crate) const LIST_BIT: u32 = 1 << 30;

impl Ref {
    fn new(region: bool, index: usize) -> Ref {
        assert!(index <= INDEX_MASK as usize, "{} space full", if region { "region" } else { "persistent" });
        Ref(if region { REGION_BIT } else { 0 } | index as u32)
    }
    #[inline(always)]
    pub(crate) fn in_region(self) -> bool {
        self.0 & REGION_BIT != 0
    }
    #[inline(always)]
    fn index(self) -> usize {
        (self.0 & INDEX_MASK) as usize
    }
}

/// Hashes the integers a memo key is made of by multiply and rotate, with no per-map seed: the keys are the kernel's own
/// ids, not attacker-chosen input (formerly `PtrHasher`; bit-vector design doc §47).
#[derive(Default, Clone, Copy)]
pub(crate) struct IdHasher(u64);
impl std::hash::Hasher for IdHasher {
    fn finish(&self) -> u64 {
        self.0.rotate_left(26)
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.write_u64(*b as u64);
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    fn write_u32(&mut self, x: u32) {
        self.write_u64(x as u64);
    }
    fn write_usize(&mut self, x: usize) {
        self.write_u64(x as u64);
    }
}
pub(crate) type IdMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<IdHasher>>;
pub(crate) type IdSet<K> = hashbrown::HashSet<K, BuildHasherDefault<IdHasher>>;
const H: BuildHasherDefault<IdHasher> = BuildHasherDefault::new();

/// A node's 32-bit hash: the tag and leaf, then each child's `Ref`, folded by multiply and rotate; the top half.
fn hash(n: &Node<Ref>) -> u32 {
    const K: u64 = 0x517c_c1b7_2722_0a95;
    let (tag, leaf) = n.tag_leaf();
    let mut h = ((tag as u64) << 32 | leaf as u64).wrapping_mul(K);
    n.for_kids(|c, _| h = (h.rotate_left(5) ^ c.0 as u64).wrapping_mul(K));
    (h >> 32) as u32
}

/// The stored 32-bit hash spread to 64 for hashbrown, which takes its 7-bit tag from the top bits: zero-extended, every
/// entry would get tag 0 and every probe would read nodes (spec, "Kernel internals").
#[inline(always)]
fn spread(h: u32) -> u64 {
    (h as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

/// Empties `v`, and gives its memory back when it held under a quarter of its capacity, so a small region after a large
/// one doesn't pay for the large one's capacity (hashbrown's `clear` costs time in the capacity; spec, "Kernel
/// internals").
fn reset_vec<T>(v: &mut Vec<T>) {
    let used = v.len();
    v.clear();
    if used < v.capacity() / 4 {
        v.shrink_to(used);
    }
}
fn reset_map<K: Eq + std::hash::Hash, V>(m: &mut IdMap<K, V>) {
    let used = m.len();
    m.clear();
    if used < m.capacity() / 4 {
        m.shrink_to(used);
    }
}

/// One space: its nodes, their side arrays and its table.
struct Space {
    nodes: Vec<Node<Ref>>,
    /// Per node, as `Expr::loose` and `Expr::free`.
    loose: Vec<u32>,
    free: Vec<u32>,
    /// Per node, the `hc::uses` slot (0: empty).
    uses: Vec<u32>,
    /// Per node, the nodes built over it, saturating at 2 (`Expr::shared`).
    parents: Vec<u8>,
    /// Each node's hash and `Ref`: 8 bytes an entry.
    table: hashbrown::HashTable<(u32, Ref)>,
}

impl Space {
    const fn new() -> Space {
        Space { nodes: Vec::new(), loose: Vec::new(), free: Vec::new(), uses: Vec::new(), parents: Vec::new(), table: hashbrown::HashTable::new() }
    }
    fn find(&self, h: u32, n: &Node<Ref>) -> Option<Ref> {
        self.table.find(spread(h), |&(g, r)| g == h && self.nodes[r.index()] == *n).map(|&(_, r)| r)
    }
    fn push(&mut self, region: bool, h: u32, n: Node<Ref>, (loose, free): (u32, u32), parents: u8) -> Ref {
        let r = Ref::new(region, self.nodes.len());
        self.nodes.push(n);
        self.loose.push(loose);
        self.free.push(free);
        self.uses.push(0);
        self.parents.push(parents);
        self.table.insert_unique(spread(h), (h, r), |&(g, _)| spread(g));
        r
    }
    fn clear(&mut self) {
        reset_vec(&mut self.nodes);
        reset_vec(&mut self.loose);
        reset_vec(&mut self.free);
        reset_vec(&mut self.uses);
        reset_vec(&mut self.parents);
        let used = self.table.len();
        self.table.clear();
        if used < self.table.capacity() / 4 {
            self.table.shrink_to(used, |&(g, _)| spread(g));
        }
    }
}

/// The region's memos, keyed by resolved `Ref` bits and emptied when it closes (they were `hc::Table`'s and
/// `ReductionCache`'s). Entries made with no region open name persistent nodes and stay valid until the next close.
pub(crate) struct Memos {
    /// (node, argument-list id, depth) -> its instantiation.
    pub(crate) inst: IdMap<(u32, u32, u32), u32>,
    /// (node, cutoff, amount) -> it shifted.
    pub(crate) shifts: IdMap<(u32, u32, i32), u32>,
    /// Node -> its weak head normal form.
    pub(crate) whnf: IdMap<u32, u32>,
    /// (closed node, depth) -> its head normal form to that depth.
    pub(crate) hnf: IdMap<(u32, u32), u32>,
    /// Node -> its normal form.
    pub(crate) nf: IdMap<u32, u32>,
    /// Argument lists of two or more nodes -> their id (`LIST_BIT | n`).
    pub(crate) arg_sets: IdMap<Vec<u32>, u32>,
    /// (node, depth) -> bounds `(lo, hi)` on its lowest loose variable from that depth (`hc::uses`).
    pub(crate) bounds: IdMap<(u32, u32), (u32, u32)>,
}

impl Memos {
    const fn new() -> Memos {
        Memos {
            inst: IdMap::with_hasher(H),
            shifts: IdMap::with_hasher(H),
            whnf: IdMap::with_hasher(H),
            hnf: IdMap::with_hasher(H),
            nf: IdMap::with_hasher(H),
            arg_sets: IdMap::with_hasher(H),
            bounds: IdMap::with_hasher(H),
        }
    }
    fn clear(&mut self) {
        reset_map(&mut self.inst);
        reset_map(&mut self.shifts);
        reset_map(&mut self.whnf);
        reset_map(&mut self.hnf);
        reset_map(&mut self.nf);
        reset_map(&mut self.arg_sets);
        reset_map(&mut self.bounds);
    }
}

struct Inner {
    persistent: Space,
    region: Space,
    /// The open region's generation; 0 while none is open. Never reused.
    epoch: u32,
    next_epoch: u32,
    /// The persistent length when the region opened; `u32::MAX` while none is open, so every persistent `Ref` is below.
    w: u32,
    /// Region index -> its persistent copy's `Ref`, `u32::MAX` for none: `persist`'s memo.
    copies: Vec<u32>,
    /// Persistent index - `w` -> the region node it was copied from.
    twins: Vec<Ref>,
}

/// This thread's two spaces and the region's memos.
pub(crate) struct Spaces {
    inner: UnsafeCell<Inner>,
    pub(crate) memos: RefCell<Memos>,
}

impl Spaces {
    pub(crate) const fn new() -> Spaces {
        Spaces {
            inner: UnsafeCell::new(Inner {
                persistent: Space::new(),
                region: Space::new(),
                epoch: 0,
                next_epoch: 1,
                w: u32::MAX,
                copies: Vec::new(),
                twins: Vec::new(),
            }),
            memos: RefCell::new(Memos::new()),
        }
    }

    #[inline(always)]
    fn get(&self) -> &Inner {
        // SAFETY: see the module doc; no `&mut` from `inner()` is live across a call to this.
        unsafe { &*self.inner.get() }
    }

    #[allow(clippy::mut_from_ref)]
    #[inline(always)]
    fn inner(&self) -> &mut Inner {
        // SAFETY: see the module doc.
        unsafe { &mut *self.inner.get() }
    }

    #[inline(always)]
    fn space(&self, r: Ref) -> &Space {
        let i = self.get();
        if r.in_region() { &i.region } else { &i.persistent }
    }

    /// The open region's generation, 0 while none is open.
    #[inline(always)]
    pub(crate) fn epoch(&self) -> u32 {
        self.get().epoch
    }

    /// The `Ref` that a handle made in generation `epoch` names now. A region `Ref` must come from the open region, or the
    /// handle is dead. A persistent one at or above `w` reads as its region twin (Invariant R).
    #[inline(always)]
    pub(crate) fn resolve(&self, r: Ref, epoch: u32) -> Ref {
        let i = self.get();
        if r.in_region() {
            assert!(epoch == i.epoch && epoch != 0, "dead handle: a term used after the scope it was built in closed (persist it, or return it from `scoped`)");
            r
        } else if r.0 >= i.w {
            i.twins[(r.0 - i.w) as usize]
        } else {
            r
        }
    }

    /// Whether [`resolve`](Spaces::resolve) would succeed.
    #[inline(always)]
    pub(crate) fn live(&self, r: Ref, epoch: u32) -> bool {
        !r.in_region() || (epoch == self.get().epoch && epoch != 0)
    }

    /// The node `r` (resolved) names.
    #[inline(always)]
    pub(crate) fn node_at(&self, r: Ref) -> Node<Ref> {
        self.space(r).nodes[r.index()]
    }
    #[inline(always)]
    pub(crate) fn loose_at(&self, r: Ref) -> u32 {
        self.space(r).loose[r.index()]
    }
    #[inline(always)]
    pub(crate) fn free_at(&self, r: Ref) -> u32 {
        self.space(r).free[r.index()]
    }
    #[inline(always)]
    pub(crate) fn parents_at(&self, r: Ref) -> u8 {
        self.space(r).parents[r.index()]
    }
    #[inline(always)]
    pub(crate) fn uses_at(&self, r: Ref) -> u32 {
        self.space(r).uses[r.index()]
    }
    #[inline(always)]
    pub(crate) fn set_uses_at(&self, r: Ref, v: u32) {
        let i = self.inner();
        let s = if r.in_region() { &mut i.region } else { &mut i.persistent };
        s.uses[r.index()] = v;
    }

    /// The node `n` over resolved children. If all its children are persistent, it is looked up in the persistent space
    /// first, taking only a hit below `w` (one at or above is a copy, whose twin the region lookup finds). Then it is found
    /// in the region or built there. With no region open, it is found or built in the persistent space.
    pub(crate) fn build(&self, n: Node<Ref>) -> Ref {
        let h = hash(&n);
        let i = self.inner();
        let mut persistent_kids = true;
        n.for_kids(|c, _| persistent_kids &= !c.in_region());
        if persistent_kids
            && let Some(r) = i.persistent.find(h, &n)
            && r.0 < i.w
        {
            return r;
        }
        let in_region = i.epoch != 0;
        debug_assert!(in_region || persistent_kids, "a region child with no region open");
        if in_region && let Some(r) = i.region.find(h, &n) {
            return r;
        }
        let ranges = {
            let (p, g) = (&i.persistent, &i.region);
            let at = |c: &Ref| if c.in_region() { g } else { p };
            n.ranges(|c| at(c).loose[c.index()], |c| at(c).free[c.index()])
        };
        n.for_kids(|c, _| {
            let s = if c.in_region() { &mut i.region } else { &mut i.persistent };
            let p = &mut s.parents[c.index()];
            *p = p.saturating_add(1).min(2);
        });
        if in_region { i.region.push(true, h, n, ranges, 0) } else { i.persistent.push(false, h, n, ranges, 0) }
    }

    /// `r` (resolved) as a persistent `Ref`. The region nodes reachable from it are copied out bottom-up, each once per
    /// region (`copies`), and every copy records its twin. The identity on a persistent `r`. The region stays usable.
    pub(crate) fn persist(&self, r: Ref) -> Ref {
        if !r.in_region() {
            return r;
        }
        let k = r.index();
        let n = {
            let i = self.inner();
            if let Some(&p) = i.copies.get(k)
                && p != u32::MAX
            {
                return Ref(p);
            }
            i.region.nodes[k]
        };
        let m = super::grow(|| n.map_kids(|c, _| self.persist(c)));
        let i = self.inner();
        let h = hash(&m);
        debug_assert!(i.persistent.find(h, &m).is_none(), "persist met a copy it did not make (Invariant I)");
        let p = i.persistent.push(false, h, m, (i.region.loose[k], i.region.free[k]), i.region.parents[k]);
        i.twins.push(r);
        debug_assert_eq!(i.w as usize + i.twins.len(), i.persistent.nodes.len());
        if i.copies.len() <= k {
            i.copies.resize(i.region.nodes.len(), u32::MAX);
        }
        i.copies[k] = p.0;
        p
    }

    /// Opens a region unless one is open; true when this call opened it.
    pub(crate) fn open(&self) -> bool {
        let i = self.inner();
        if i.epoch != 0 {
            return false;
        }
        i.epoch = i.next_epoch;
        i.next_epoch = i.next_epoch.checked_add(1).expect("region generations ran out");
        i.w = i.persistent.nodes.len() as u32;
        true
    }

    /// Closes the open region: its nodes, `copies`, twins and memos are emptied, and every handle into it is dead.
    pub(crate) fn close(&self) {
        let i = self.inner();
        i.epoch = 0;
        i.w = u32::MAX;
        i.region.clear();
        reset_vec(&mut i.copies);
        reset_vec(&mut i.twins);
        self.memos.borrow_mut().clear();
    }

    /// Nodes in both spaces (`take_built`'s count of new nodes is this one's growth).
    #[cfg(feature = "record-defeq")]
    pub(crate) fn len(&self) -> usize {
        let i = self.get();
        i.persistent.nodes.len() + i.region.nodes.len()
    }

    #[cfg(test)]
    fn persistent_len(&self) -> usize {
        self.get().persistent.nodes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::super::Node::*;
    use super::*;

    #[test]
    fn a_stored_node_is_24_bytes() {
        assert_eq!(std::mem::size_of::<Node<Ref>>(), 24);
    }

    #[test]
    fn the_persistent_space_dedups_and_keeps_ranges() {
        let s = Spaces::new();
        let v = s.build(Var(3));
        assert_eq!(s.build(Var(3)), v);
        assert!(!v.in_region());
        let f = s.build(Free(2));
        let a = s.build(App(v, f));
        assert_eq!((s.loose_at(a), s.free_at(a)), (4, 3));
        let l = s.build(Lam(f, s.build(Var(0))));
        assert_eq!((s.loose_at(l), s.free_at(l)), (0, 3));
        let z = s.build(Sort(0));
        assert_eq!(s.loose_at(s.build(Pair(v, z, z))), 3, "a pair's family sits under a binder");
    }

    #[test]
    fn a_region_dedups_and_prefers_old_persistent_nodes() {
        let s = Spaces::new();
        let old = s.build(Var(1));
        assert!(s.open());
        assert!(!s.open(), "a nested open joins the region");
        assert_eq!(s.build(Var(1)), old, "a persistent hit below w");
        let v = s.build(Var(7));
        assert!(v.in_region());
        assert_eq!(s.build(Var(7)), v);
        let a = s.build(App(v, old));
        assert!(a.in_region());
        assert_eq!(s.build(App(v, old)), a);
        s.close();
    }

    #[test]
    fn persist_copies_once_and_records_twins() {
        let s = Spaces::new();
        assert!(s.open());
        let g = s.epoch();
        let v = s.build(Var(9));
        let t = s.build(App(v, v));
        let before = s.persistent_len();
        let p = s.persist(t);
        assert_eq!(s.persist(t), p, "memoised");
        assert_eq!(s.persistent_len(), before + 2, "Var(9) and the App, once each");
        assert!(!p.in_region());
        assert_eq!(s.resolve(p, g), t, "a copy reads as its twin while the region is open");
        // Invariant I: the same structure built again is the region node, not the copy at or above w.
        assert_eq!(s.build(Var(9)), v);
        assert_eq!(s.build(App(v, v)), t);
        s.close();
        assert_eq!(s.resolve(p, 0), p);
        let App(c, d) = s.node_at(p) else { panic!("persist changed the constructor") };
        assert!(c == d && !c.in_region() && s.node_at(c) == Var(9));
        assert!(s.open());
        assert_eq!(s.build(Var(9)), c, "the next region finds the copy below its w");
        s.close();
    }

    #[test]
    #[should_panic(expected = "dead handle")]
    fn a_ref_from_a_closed_region_is_dead() {
        let s = Spaces::new();
        assert!(s.open());
        let (r, g) = (s.build(Var(5)), s.epoch());
        s.close();
        assert!(!s.live(r, g));
        assert!(s.open());
        let fresh = s.build(Var(6));
        assert_eq!(fresh.0, r.0, "the new region reuses the index, so only the generation tells them apart");
        s.resolve(r, g);
    }

    #[test]
    fn parents_count_builds_not_hits() {
        let s = Spaces::new();
        assert!(s.open());
        let x = s.build(Var(3));
        let a = s.build(App(x, x));
        assert_eq!((s.parents_at(x), s.parents_at(a)), (2, 0));
        let y = s.build(Var(4));
        let r = s.build(Refl(y));
        assert_eq!(s.build(Refl(y)), r);
        assert_eq!(s.parents_at(y), 1, "a hit adds no parent");
        s.close();
    }
}
```

- [ ] **Step 2: Run** `CARGO_TARGET_DIR=target/s3 cargo test --lib -j 8 spaces::`. Expected: 6 passed. Also run it
  under Miri if `cargo miri` is installed (`cargo +nightly miri test --lib spaces::`), as a check on the `unsafe`
  contract. If Miri isn't installed, say so; don't install it.
- [ ] **Step 3: Commit** ("kernel: spaces.rs, the id arena's two spaces (Stage 3 B1), unused until B2").

### Task 5 (B2): the arena behind the handle

**Files:** `src/kernel.rs`, `src/kernel/spaces.rs` (drop the `allow`), `src/kernel/tests.rs`, `src/kernel/bin.rs`
(test), `tests/church_bv/encoding.rs` (one test), `benches/proofs.rs`. One atomic switch, with the same compile gates
as Task 2 (Steps 4-8).

- [ ] **Step 1: The handle.** In `kernel.rs`, replace the Phase A `Expr`, `Header`, `Drop for Header`, the stub
  `Spaces` and `with_spaces` with:

```rust
/// A term: a node id in this thread's spaces (`spaces.rs`) and the region generation it was made in. `Copy`, 8 bytes,
/// neither `Send` nor `Sync`. A handle from a region that has closed is dead: reading it panics ("dead handle"), and
/// `Debug` prints `<dead handle>`. Persist what must outlive the region ([`persist`], or return it from [`scoped`]).
#[derive(Clone, Copy)]
pub struct Expr {
    r: Ref,
    epoch: u32,
    _thread: std::marker::PhantomData<*const ()>,
}

impl Expr {
    #[inline(always)]
    fn at(r: Ref, epoch: u32) -> Expr {
        Expr { r, epoch, _thread: std::marker::PhantomData }
    }
    // node / loose / free / shared: unchanged from Phase A (each `with_spaces(|s| s.<same>(self))`).
}

thread_local! {
    static SPACES: Spaces = const { Spaces::new() };
}

/// Runs `f` with this thread's spaces.
#[inline(always)]
pub(crate) fn with_spaces<R>(f: impl FnOnce(&Spaces) -> R) -> R {
    SPACES.with(f)
}

pub(crate) type Key = u32;
pub(crate) type Aid = u32;

/// The kernel's handle-level reads and builds (`spaces.rs` works on `Ref`s).
impl Spaces {
    #[inline(always)]
    fn res(&self, e: &Expr) -> Ref {
        self.resolve(e.r, e.epoch)
    }
    #[inline(always)]
    pub(crate) fn node(&self, e: &Expr) -> Node<Expr> {
        let g = self.epoch();
        self.node_at(self.res(e)).map_kids(|r, _| Expr::at(r, g))
    }
    pub(crate) fn mk(&self, n: Node<Expr>) -> Expr {
        #[cfg(feature = "record-defeq")]
        BUILT.with(|c| c.set(c.get() + 1));
        let r = self.build(n.map_kids(|c, _| self.res(&c)));
        Expr::at(r, self.epoch())
    }
    #[inline(always)]
    pub(crate) fn loose(&self, e: &Expr) -> u32 {
        self.loose_at(self.res(e))
    }
    #[inline(always)]
    pub(crate) fn free(&self, e: &Expr) -> u32 {
        self.free_at(self.res(e))
    }
    #[inline(always)]
    pub(crate) fn shared(&self, e: &Expr) -> bool {
        self.parents_at(self.res(e)) > 1
    }
    #[inline(always)]
    pub(crate) fn same(&self, a: &Expr, b: &Expr) -> bool {
        self.res(a) == self.res(b)
    }
    #[inline(always)]
    pub(crate) fn key(&self, e: &Expr) -> Key {
        self.res(e).0
    }
    #[inline(always)]
    pub(crate) fn from_key(&self, k: &Key) -> Expr {
        Expr::at(Ref(*k), self.epoch())
    }
    // uses_slot / set_uses_slot: Phase A's packing over `uses_at` / `set_uses_at` of `self.res(e)`.
}

pub fn node_key(e: &Expr) -> u64 {
    with_spaces(|s| s.key(e) as u64)
}
```

  Then:
  - **`PartialEq for Expr`:** `with_spaces(|s| s.same(self, other))`. `Eq` stays; there is no `Hash`.
  - **`Debug for Expr`:** if `!s.live(self.r, self.epoch)`, write `<dead handle>`; otherwise `write_expr(&s.node(self),
    ..)`.
  - **`take_built`:** with `record-defeq`, it reads `BUILT` and a `NEW` counter. `NEW` is the persistent and region
    lengths' growth, read through `Spaces::len` (Task 4's code).
  - **`PExpr`:** `#[derive(Clone, Copy, PartialEq, Eq, Hash)] pub struct PExpr(Ref, PhantomData<*const ()>)`. Its
    `Eq` and `Hash` are the persistent `Ref`'s, so they are stable, and it is `!Send` (spec, "PExpr"). `get(&self) ->
    Expr` is `with_spaces(|s| Expr::at(self.0, s.epoch()))`, `From<PExpr> for Expr` the same, and `Debug` through `get`.
  - **`persist`:** `with_spaces(|s| PExpr(s.persist(s.res(&e)), PhantomData))`.
  - **`scoped`:**

```rust
pub fn scoped<R: Escape>(f: impl FnOnce() -> R) -> R {
    struct Close;
    impl Drop for Close {
        fn drop(&mut self) {
            with_spaces(|s| s.close());
        }
    }
    if !with_spaces(|s| s.open()) {
        return f();
    }
    let close = Close;
    let r = f().escape();
    drop(close);
    r
}
```

  - **`intern_generation`:** `with_spaces(|s| s.epoch())`.
  - **`segment_switches`, `grow`, `stack_ok`, `on_segment`:** unchanged. `grow_slow`'s drop use goes with `Drop`.

- [ ] **Step 2: `hc` on the arena.** `mod hc` keeps `uses`, `lowest_loose`, `args_id`, `low`/`height_at_most`,
  `LARGE`/`exceeds`/`large` and the memo accessors, each taking `s` and keying by `s.key(..)`.
  - **Memo accessors** (`inst_get/put`, `shift_get/put`, `whnf_get/put`, `hnf_get/put`, plus the new `nf_get/put`)
    read and write `s.memos.borrow()`/`borrow_mut()` and return `Option<Expr>` through `s.from_key`. A borrow never
    lives past the accessor. `inst_get`/`inst_put` take `aid: Option<Aid>` and are no-ops on `None`.
  - **`uses`:** reads `s.uses_slot`, then `memos.bounds`.
  - **`args_id(s, args) -> Option<Aid>`:**
    - one argument: `Some(s.key(a))`;
    - several: their keys looked up in `memos.arg_sets`, and a new list gets `LIST_BIT | n` with `n` the set's size
      before the insert;
    - it never returns `None` in Phase B (the `Option` stays for one signature);
    - `assert!(n < LIST_BIT)`.
  - **`exceeds`:** an `IdSet<Key>` walk with `for_kids`.
  - **Deleted:** `Table`, `TABLE`, `NodeKey`, `key_of`, `intern`, `intern_as`, `canon`, `canonical_inputs`, `pin`,
    `keep`, `WARM_UP`, `CALLS`, `GENERATION`, `NEXT_GENERATION`, `generation()`, `active()`, `activate`, `Scope` (with
    its six direct test uses), `DEPTH` and `hc::scoped`.
- [ ] **Step 3: Reduction and typing.**
  - **Deleted with their parameters:** `ReductionCache` (and every `cache` parameter), `PtrKey`, `PtrHasher`,
    `PtrMap`/`PtrSet` (callers use `IdMap`/`IdSet`), `eq_noting` and `Expr::canonical`. All memos go through `hc`'s
    accessors.
  - **`whnf_in(s, e)`:** `hc::whnf_get`, else `whnf_step(s, e).unwrap_or(*e)` and `hc::whnf_put`.
  - **`nf_in(s, e)`:** likewise through `hc::nf_get/put`.
  - **`hnf_rc`:** `hc::hnf_get/put` only (the `table`/`cache` branch goes).
  - **`conv(s, a, b)`:** `if s.same(a, b) { return true; } conv_whnf(s, &whnf_in(s, a), &whnf_in(s, b))`.
  - **`def_eq`:** `scoped(|| with_spaces(|s| def_eq_in(s, a, b)))`.
  - **`infer_in`:** `scoped(|| with_spaces(|s| infer_node(..)))`, with the `free` check first, as today.
  - **`check_in`:** `scoped(|| with_spaces(|s| { let large = hc::large(s, e, expected); let body = || { .. };
    if large { on_segment(CHECK_SEGMENT, body) } else { body() } }))`, where `body` infers `expected`'s sort and checks
    `e`, both on the inputs as given.
  - **Public `whnf` and `normalize`:** `scoped(|| with_spaces(|s| whnf_in(s, e)))`, and likewise with `nf_in`. They
    copy their result out when outermost (spec, "Kernel internals").
  - **`typecheck`:** `scoped(|| infer(..).map(|t| with_spaces(|s| nf_in(s, &t))))`.
  - **`brief_nf`:** `Nf(Expr)`, whose `Debug` reduces through `with_spaces(|s| whnf_in(s, &self.0))`.
  - **`InferCache`:** maps are `IdMap`s keyed by `Key` (`u32`), and `info`'s `Option<Key>` stays.
  - **Probes:** the record-defeq `SEEN` keys by `(Key, u32)`.
- [ ] **Step 4: Wire `spaces.rs` in.** `use spaces::{IdMap, IdSet, Ref, Spaces, LIST_BIT};`. Remove the
  `#[allow(dead_code)]`.

  **Compile gates 1-2** as in Task 2: `cargo build --lib -j 8`, and again with `--features record-defeq`.

- [ ] **Step 5: Tests.**
  - **Deleted, since B removes the mechanism each asserts:**
    - `memo_sources_outlive_their_callers` (`pin`/`keep`);
    - `args_id_is_the_same_for_a_canonical_argument_and_its_twin` (canonical twins);
    - `dropping_a_deep_term_does_not_overflow_the_stack` (handles are `Copy`, and nothing is freed per node);
    - `infer_memo_changes_no_answer` and `shares_nothing`: under hash-consing, the "unshared copy" is the same node,
      so the test compares a term with itself. The kernel fuzzers and the sweep gate still check answers.
  - **Ported:**
    - `args_id_is_stable_for_short_and_long_lists`: `Option<u32>`, and the `% 2 == 1` assert (Phase A's lists get
      odd ids, addresses being even) becomes `s & LIST_BIT != 0 && l & LIST_BIT != 0`;
    - `intern_finds_equal_nodes_after_growth` (on `mk` inside `scoped`);
    - `uses_slot_is_free_and_agrees_with_the_walk` (`scoped` instead of `hc::Scope` + `activate`);
    - `uses_bounds_agree_with_lowest_loose`;
    - `whnf_memo_outlives_one_def_eq_in_a_scope` (reads `memos.whnf`);
    - `cong_n_shares_shifted_copies_outside_a_scope` (`intern_generation() == 0` in place of `hc::generation()`);
    - every `node_key` identity assert. It now also holds by hash-consing, so these tests check values and keys
      together. `whnf_keeps_the_stuck_part_it_was_given` and `whnf_keeps_the_arguments_it_was_given` keep their
      asserts. Their docs, which say "`ReductionCache` is keyed by pointer", are reworded to "the memos are keyed by
      node".
  - **`bin_round_trips_and_shares_nodes`:** the plain encoding now equals the interned one, because the persistent
    space is hash-consed. Assert `bs.len() == b.len()` and update the comment.
  - **`constants_are_built_once_per_generation`** (encoding.rs): the second region's rebuilt gate finds the copy that
    `scoped` persisted from the first. Assert `node_key(&a.1) == node_key(&first.1)`, and say so in its doc.
  - **New, in `kernel/tests.rs`:**

```rust
/// A handle used after the region it was built in closed panics instead of naming another term (spec, "Soundness" 2).
#[test]
#[should_panic(expected = "dead handle")]
fn a_handle_from_a_closed_region_is_dead() {
    let kept = std::cell::Cell::new(None);
    scoped(|| kept.set(Some(app(var(0), var(1)))));
    let e = kept.get().unwrap();
    let _ = e.node();
}

/// `Debug` on a dead handle reports it instead of panicking, so an `assert_eq!` that prints one still says what failed.
#[test]
fn a_dead_handle_prints_as_dead() {
    let kept = std::cell::Cell::new(None);
    scoped(|| kept.set(Some(app(var(0), var(1)))));
    assert_eq!(format!("{:?}", kept.get().unwrap()), "<dead handle>");
}
```

  - **`benches/proofs.rs`:** each gcd bench's iteration runs in its own region: `b.iter(|| tatic::kernel::scoped(|| {
    black_box(prove_..(..).unwrap()); }))`. The proof is dropped inside, so the persistent space doesn't keep a copy
    per iteration (spec, "Risks").
  - **Gates:** compile gates 3-4 and the full suite, as Task 2 Steps 6-8. Expected counts against
    `s3_a_counts.txt`: lib = A's lib count + 6 (B1's `spaces::` tests) - 4 (deleted above) + 2 (the dead-handle
    tests), so A's + 4; every other binary unchanged. Any other difference stops the task.
- [ ] **Step 6: `clippy --fix`.** `CARGO_TARGET_DIR=target/s3 cargo clippy --fix --all-targets --allow-dirty -j 8`
  turns `.clone()` on `Expr`/`PExpr` into copies. Read `git diff --stat` and a sample of the hunks. Then run `cargo
  clippy --all-targets -j 8`: no more warnings than the baseline. Rerun the full suite.
- [ ] **Step 7: Commit** ("kernel: terms are ids in two spaces (id arena Stage 3, Phase B)", listing what B deleted and
  the tests deleted and changed).

### Task 6 (B3): Stage 3 gates, timing, docs

- [ ] **Step 1: Exes.** Build church_bv and the proofs bench at Task 5's commit, and copy them to `$TEMP/bv_s3_b.exe`
  and `$TEMP/proofs_s3_b.exe`.
- [ ] **Step 2: Identical outputs.** `s3_seq.sh s3b $TEMP/bv_s3_base.exe $TEMP/bv_s3_b.exe`, compared as in Task 3
  Step 2 under the Global Constraints' rule. If a lemma-cache file differs, the `LEMMA_CACHE` lines' counts must be
  equal; report the size difference.
- [ ] **Step 3: Timing.** Load and RTP before each block; no other session's job on the cores (`Get-Process` for
  `cargo`, `rustc` and test exes).
  - **`proof_cost_split`:** `cpu_ab.ps1 $TEMP\bv_s3_base.exe - 8 $TEMP\bv_s3_b.exe`. About 1.5 minutes.
  - **Rule 33's law:** `law_ab.sh $TEMP/bv_s3_base.exe $TEMP/bv_s3_b.exe 3 8 16 32 64`. The duration comes from Task
    1's spike: (spike n=8 + spike n=64) × 2 arms × 3 pairs, plus about as much again for n=16 and 32. Spike
    (2026-10-14, base exe, `LAW_REPS=3`, pinned): n=8 1.5 s wall (check min 60 ms), n=64 3.9 s wall (check min 599 ms),
    so about 0.3 s and 1.1 s per extra rep. At `LAW_REPS=5`: about 4 + 4 s per pair at n=8, 6 + 6 s at n=64, so the
    whole block is about 2 minutes.
  - **Sweep CPU and peak commit:** `sweep_job.ps1` three rounds per arm, alternating, one fresh PowerShell each:
    `powershell -NoProfile -File docs\runs\2026-10-12\scripts\sweep_job.ps1 $env:TEMP\bv_s3_<base|b>.exe large <r>`.
    About 25 s a run.
  - **gcd benches:** `$TEMP/proofs_s3_base.exe --bench gcd` and `$TEMP/proofs_s3_b.exe --bench gcd`, three each,
    alternating, pinned. Base runs today's bench code (no `scoped`, so the lazy table stays off, as today's callers
    run it). B runs its region per iteration.
  - **Gates (spec):**
    - gcd benches within 10% of base, median of the three per bench;
    - every other number is reported, not gated: the spec's gate is "timed A/B with peak commit".
  - **Which governs:** a failed gate (identity, suite, or gcd) means the branch is not ready, whatever the timing
    says. With the gates passed, the decision rule below decides what the report recommends: keep, or profile first.
  - **Decision rule for the report:** the port is worth keeping if rule 33 at n=64 is faster and `proof_cost_split`
    is not slower beyond its spread (3.63-3.98 s across earlier rotations). Otherwise report which number lost, with
    one profile (SAMPLY.md) of the losing case before proposing anything.
- [ ] **Step 4: Docs.**
  - **`docs/tier-cycle.md`:** an entry "Id arena Stage 3 (date)". What changed (both phases), the identity gates, the
    timing tables with load and RTP (A informational, B gated), the decision rule's outcome, and the parked items
    (departure 2's raw-`Ref` walks; the spec's parked list).
  - **The runs README:** rows for `s3a_*`, `s3b_*`, `law_ab`, `sweep_job` and the benches.
  - **`docs/learned-vs-fixed.md`:** a row only if a learned or fixed part changed (expected: none; say so).
  - **The spec** (main checkout, not committed): Stage 3 marked done with the numbers, and departures 1-13.
  - **This plan's status line.**
  - Commit the tracked docs ("Docs: id arena Stage 3 ..." with the headline numbers).
- [ ] **Step 5: Clean up.** Remove `$TEMP/bv_s3_*.exe`, `$TEMP/proofs_s3_*.exe`, `$TEMP/s3_*_counts.txt`,
  `$TEMP/s3_base_clippy.txt`, `$TEMP/kk/law_run.txt` and the worktree's `target/s3`. Keep `$TEMP/kk/s3*` and
  `law_ab.txt`. Check `Get-Process` for leftover test exes and cargo.
- [ ] **Step 6: Stop.** Report the gates and numbers, and ask for the merge and push go-aheads: `id-arena-stage2` and
  `id-arena-stage3` into main, plus main's three unpushed doc commits.

## Risks

- **A2 and B2 are large atomic edits** (about 630 sites, plus kernel.rs's internals). Each has ordered compile gates.
  If one stalls, `git stash` keeps the work, and the plan can fall back to porting one file per sub-commit behind
  `#[cfg(any())]`-free shims. That fallback is a ruling to ask about, not to take silently, since it means
  temporary shims.
- **Phase A is slower.** Owned children per read, the larger block, and merged memos. Only B's numbers decide.
- **Every read resolves in B** (departure 2). If `resolve` shows in the profile, the parked raw-`Ref` walks are the
  fix.
- **Small proofs pay full interning** (departure 11). The gcd gate measures it. If it fails, the outermost region's
  memos and table sizes are where to look (the shrink rule), before anything like a lazy table returns.
- **A store of `Expr` caught only at run time.** Stage 2's `stale` count was 0 on `proof_cost_split` and a sweep, and
  the B gates run the suite and two sweeps.
- **The `UnsafeCell` contract.** It is kept by structure (no reference escapes a method), tested by B1's unit tests,
  and by Miri when it is available.

## Adversarial review

Four rounds (2026-10-14), each finding checked against tatic-s2 before it was applied:

1. **Self:**
   - Confirmed: `Escape` covers `Duration`, `Postulates` holds `PExpr`, and kernel_lazy's memo lives one call and
     holds its nodes, so `node_key` is safe there in both phases. The tests the plan deletes or ports exist as
     described.
   - Fixed: `Spaces::build`'s mutable and immutable borrow of the spaces at once; Task 5's count wording.
2. **Sonnet, full plan against the code:**
   - Fixed:
     - `gen` is reserved in edition 2024, so the code says `epoch`;
     - the count deltas: lib -1 in A, since the copy-volume test is feature-gated, and the baseline is re-recorded
       after `law_time`;
     - `infer_memo_changes_no_answer` is ported in A and deleted in B;
     - `args_id`'s odd-id assert;
     - `PExpr: Hash` and `!Send`;
     - one lemma-cache rule for both phases;
     - the stale `s3_done.txt` marker;
     - the nonexistent `examples/`.
   - Ruled against: resetting persistent parent counts (departure 3 says why). No soundness hole found.
3. **Sonnet, Phase A preservation, literal code, scripts, spec drops:**
   - Fixed:
     - the `for_kids` lifetime (`same_shape` stores the refs);
     - the `kernel::mk` clash with church_bv's `encoding::mk` (renamed `church_tuple`);
     - `PtrKey: Clone`;
     - departures 12 (`IdSet` against the bitset) and 13 (A's memo-skip change);
     - which of the gates and the decision rule governs.
   - Nothing material in answer preservation, field orders, the examples, or the scripts.
4. **Sonnet, compile-level read of every block and cross-task names:**
   - No compile errors.
   - Fixed (minor): `relevant_signature` reads `info` by reference; `Spaces::len` is in Task 4's code; the two
     `whnf_keeps_*` tests' docs.
   - Nothing material, so the loop stopped.
