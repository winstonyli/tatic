---
status: done
---

# Codebase review (2026-10-03)

Scope: clippy over all targets, metrics, and a read of `tests/church_bv.rs` (the Church bit-vector library and
the rule miner). The rest of `src/` was skimmed by one read-only subagent (see below).

## Done

- **Module split (option A).** `tests/church_bv.rs` is now `tests/church_bv/{main,encoding,rewrite,machine,search}.rs`
  (contiguous ranges, so each test stays next to its code; items made `pub`, modules `use super::*`). Test names gain
  a module prefix (`search::rule_miner`); substring filters in the experiment scripts still match, and
  `scripts/miner_summary.sh` (`--exact`) was updated. Older docs still say `tests/church_bv.rs`: read that as the
  directory. Still 44 passed, 42 ignored. Layers are only roughly separated (the ranges follow file order).
- **`MinerConfig` (option B).** `rule_miner` reads its `RULEMINER_*` switches once. Found a hidden asymmetry:
  `RULEMINER_MIDPOINT` defaults to 3 for the `midpoint` proposer and 0 for the final probe; it is now an `Option`.
  Checked on the shl family: output identical to the pre-change build (timings aside). The midpoint paths were
  not re-run in that check. Later re-run on the split build (deep add3, 64 stragglers): `mined` 51, `midpoint` 6,
  `goal` 27 covered, matching the earlier numbers (CPU about 40% from other load, Defender RTP off; counts only, no timings).
- **Clippy (option E).** 0 warnings in the test target (type aliases `BitPair`, `BitTriple`, `BitsDyn`, `Bits4`,
  `DdBuild`, `ScoredRule`; collapsed ifs).
- `cargo clippy --fix` also edited `src/kernel.rs` once (redundant closure); reverted.

- `tests/church_bv.rs` clippy `erasing_op` (deny-level; `0 * v as u32` in a closure) fixed (first commit of the day). The test target now has
  0 clippy errors; tests: 44 passed, 42 ignored.

## Reported, not changed

- `src/kernel.rs:1297`: `if n < WARM_UP` is always false; deny-level, so `cargo clippy --all-targets` fails for
  the lib test target. Also "very complex type" at 953, 1009, 1010, a redundant closure at 1219 and a same-type cast
  at 3679. The kernel is off limits by standing rule; the owner decides.

## Findings in `tests/church_bv.rs` (about 6,600 lines, about 300 items, 88 tests of which 42 are `#[ignore]` probes/miners)

1. **Four layers in one file:** Church encoding and proofs (1â€“2100); `Term`, rewriter, rules (2100â€“3400); machines and
   encoding search (3400â€“5300); miner and tools (5300â€“end).
2. **Three rule-set mechanisms:** the `PROMOTED` const with `promoted_rules()`, `rule_set()` (files in
   `scripts/data`, selected by `RULESET`), and the run-time `EXTRA_RULES` thread-local. `rules()` stitches them.
3. **`rule_miner` is one function of about 400 lines** with about 25 env switches (about 61 env vars in the file),
   documented only in scattered doc comments.
4. **Magic operator indices** 0â€“7 (57 `Term::Op([0-7]` sites) instead of an enum.
5. **Fixed mining shape:** n=4 and 2â€“3 variables. The rules themselves are width-generic (proved at n=4..64 for the
   promoted sets), so this is a miner limitation, not a library one.
6. **Duplicate constant folding:** old `folds_constants` and new `fold_rule` overlap.
7. **Clippy warnings:** 19 in `church_bv.rs` (13 "very complex type", 8 collapsible if, 2 redundant closure,
   singles); mechanical.

## Generalization status

- Width: `low_bits(n)` replaced `(1u128 << n) - 1`; library and rules verified up to n=128 (u128 limit in `interp`).
- Families: add/sub, mul, shl, shr, lt all share one rewriter. The midpoint and goal proposers work on add/sub-heavy
  families only (mul closed by `mined`; shl/lt/shr gain 0/0/1).
- Rule transfer: promoted sets (`add3_mm`, `mix3_mm`, `add3_nl`, `mix3_nl`) prove 20/20 laws at every n in 4..64.

## Refactor options (none started; need a go-ahead)

| Option | Pros | Cons |
|---|---|---|
| A. Split into modules (`tests/church_bv/{encoding,term,rules,machine,miner}.rs`, or a dev crate) | Layers become navigable; faster incremental builds; reviewable diffs | Large mechanical diff; `include_str!` paths and the experiment scripts' test names (`church_bv::...`) change; history blame is lost |
| B. `MinerConfig` parsed once from env | Documents every switch in one place; testable; shrinks `rule_miner` | Touches the hot experiment path; risk of silently changing defaults (verify with a baseline run: deep add3 `mined` 51/64) |
| C. `Op` enum replacing indices 0â€“7 | Removes magic numbers and non-exhaustive matches | 57+ sites; `Term::Op(usize, ..)` also appears in the data files' parser and scripts |
| D. Unify rule sources into one `RuleSet` value | One place to ablate, load, log | `PROMOTED` is used by tests as a baseline; `RULE_BUDGET` and `RULE_SEEN` thread-locals ride along |
| E. Clippy cleanup only | Cheap, safe | Does not address structure |

**Option D, after reading the code (`rewrite.rs:465-605`): not worth doing.** `rules()` already merges all sources into one
`Vec<Rule>`; the four tiers differ on purpose (built-in, `PROMOTED` stable and ablatable as `promoted`, `RULESET`
file loaded from the environment, `EXTRA_RULES` the miner's scratch space) and each has its own `ABLATE` name. A
`RuleSet` type would add indirection without removing a mechanism. Doc comments on the four tiers would give most of
the benefit. **Option C, done in a lighter form:** named constants `ADD..SHR1` for the `Term::Op` indices, used at every pattern and
`*o == N` site (about 70 sites); arithmetic uses of the index (`OPS[o]`, `0..5` loops, `op(0, ..)` closures) keep
plain numbers. A real enum would also need `From<usize>` plumbing for those; not worth it yet. Checked: tests
unchanged, shl miner output identical.

Recommended order: E, then B (smallest risk, biggest readability gain), then D, then A; C last.

- **`proof.rs` tests** (83, about 3.7k lines) moved to `src/proof/tests.rs` as a child module (no visibility changes).
  Production code then split along its section banners into `src/proof/{tail,universal,hardening,instance,closures,per_instance}.rs`
  (`proof.rs` keeps the module docs, `ArithPostulates`, `setup`/`finish`, `prove_pure_expr`; children `use super::*`,
  items `pub(super)`, public items re-exported with `pub use`). Public API unchanged; all targets build and pass.
- **Duplicate pairs diffed.** `denote_closure` / `denote_closure_typed` were one algorithm (differences: the self-call
  context, and a bare `Term::Rec` accepted only without one); merged, `denote_closure` is now a wrapper
  (-232 lines, all tests pass). `clo_eq_ref_if_tree` / `clo_eq_ref_pap` share about half their lines but differ in
  structure; `resolve_closure_if_tree` / `resolve_closure_shape_to_leaf` are almost entirely different, so the
  subagent's duplicate claim was wrong there. Neither pair was changed.
- **`kernel.rs`:** `WARM_UP` split into two cfg consts and an `#[allow(clippy::absurd_extreme_comparisons)]` at the
  comparison (the split alone does not silence the lint: clippy evaluates the constant). `cargo clippy --all-targets`
  now has no errors.
- **Long `proof/` functions, measured and left alone.** Eight are over 120 lines; by code lines (comments and blanks
  excluded): `build_universal` 271, `denote_with_placeholders` 179, `denote_closure_typed` 177,
  `resolve_closure_shape_to_leaf` 145, `build_clo_call_bridge` 132, `eval_and_prove_direct_call` 124,
  `resolve_closure_if_tree` 95, `eval_and_prove_call_over` 76. `build_universal` is a linear script of closures that
  share one `arith` state and feed each other; splitting it needs a context struct threading about a dozen
  closures. High risk, low payoff; revisit only if one needs to change.
- `syntax::print` prints a free variable as `#i` instead of panicking (test added).

## Review of the rest of `src/` (subagent, grep and spot reads only; treat as leads, not verified)

Spot-checked by me afterwards: `syntax.rs:648` (unchecked `names[len-1-i]`, real; whether any caller can pass an
open term is not checked), `proof.rs:252` (`.expect`, real), the two step budgets (`MAX_STEPS` and
`DynBudget { steps: 200 }`, equal by comment only, real), unused `_param_types` (real). **Correction:** the budget
comment is not stale: it says 200 is now a cost bound, not a stack-safety bound.

Not assessed: `typing.rs`, `specialise.rs`, `spec_check.rs` logic. `kernel.rs` excluded.

1. `proof.rs` (6.7k production + 3.7k test lines): section banners at about :487, :628, :763, :1926, :3276, :5943 suggest
   a `proof/` directory (tail, universal, instance, closures, dyn_eval, tests).
2. Oversized functions in `proof.rs`: `build_universal` (:1504, about 410 lines), `denote_closure` (:5600, 270),
   `resolve_closure_shape_to_leaf` (:2643, 256), `denote_with_placeholders` (:961, 236), others 130–210. Also
   `jit.rs` `compile_verify_and_apply` (:225, 156), `syntax.rs` `lex` (:118, 141).
3. Likely duplicates: `clo_eq_ref_if_tree` / `clo_eq_ref_pap`; `resolve_closure_if_tree` /
   `resolve_closure_shape_to_leaf`; `denote_closure` / `denote_closure_typed`; three "peel lambdas" helpers
   (`compile.rs:515,528`, `specialise.rs:125`); hand-rolled de Bruijn shift/subst in `spec_check.rs:190,208`
   (grep `term.rs`/`kernel.rs` first); `MAX_STEPS = 200` (`proof.rs:588`) kept equal to `DynBudget.steps` by a comment only;
   repeated wasm emission sequences in `lower_wat.rs`.
4. Hard-coded limits: `lower_wat.rs` memory model (i32 pointers, 8-byte slots, 65536 pages, about 30 sites);
   `compile.rs:381` `MAX_TREE_NODES = 16_384`; `jit.rs:72` `SAMPLE_ARGS`; `proof.rs:588,3030` budgets whose
   comment says they are now cost bounds only.
5. Panics: `syntax.rs:648` index underflow printing an ill-scoped term; `proof.rs:252` `.expect` when
   `collect_literals` misses a literal; unchecked `as u32` casts in `compile.rs` (:224, :327, :339, :545, :683).
6. Dead/stale: `clo_eq_ref_pap` has an unused `_param_types`; step-budget comment narrates history; RELATED_WORK
   section numbers in comments will drift; `compile.rs` is 60% tests, `jit.rs` about 65%.

## Loose ends

- `idx.txt` (12 bytes, `[4566, 4596]`, untracked, referenced nowhere) was scratch output; deleted.
- The `src/` findings above come from a skim, and no item in it has been checked by me.
- The 42 ignored tests are not run by default; refactors must be checked against the baseline experiment numbers,
  not just `cargo test`.

## Kernel simplification (2026-10-04, authorized by the owner)

`src/kernel.rs` went from 5,835 to 2,570 lines with no change to checking code; all 428 tests pass, clippy is clean with and without `record-defeq`.
- Tests moved to `src/kernel/tests.rs` (79 tests). The node-size test is now `a_node_is_64_bytes` and skipped under `record-defeq` (its probe field adds a word; it failed there before this change too).
- `Postulates`, `Scope`, `Binder`, `NatPostulates` moved to `src/kernel/postulates.rs`, re-exported (`pub use`), so paths are unchanged; fields the tests read are `pub(super)`.
- `hc_probe` (the simulated intern-table probe) moved to `src/kernel/hc_probe.rs`, built only with `record-defeq`. The 41 `record-defeq` hooks inside the checker stay (counters, defeq log); removing them would end the replay experiments of the bit-vector note §19-§51.
- The `hashcons` feature is gone: hash-consing is unconditional. The off switch had still built and passed all kernel tests before removal (106), so this removes an A/B option, not a broken path. The bit-vector note's mentions of `--no-default-features` describe the old build.
- `kernel_lazy` is compiled only for tests and `record-defeq` (its callers); the header of `kernel.rs` was refreshed.

### Shared-carry proof (option A of the rework survey) and a correction

`add_identity_proof_shared` (`tests/church_bv/encoding.rs`) binds every carry and its proof in the proof body, `(\c pc. rest) (carry a c_prev) proof`, so no term or type the body builds mentions an inlined carry; stated over `add_shared`. It checks at n = 1, 2, 3, 4, 8 on both operand orders and rejects `rhs = 1` (test `shared_carry_proof_checks_and_rejects_wrong_statements`). Timing, same exe, alternating, release, CPU 31%, RTP off, BelowNormal (`logs/shared_carry.out`; best of two): n=16 14.7 ms shared against 15.4 inlined, n=32 41.9 against 39.7, n=64 114 against 134. **No difference**, and both are about 100 times faster than the n^3 premise: the kernel-rework survey's recommendation rested on the 14-20 s at n=64 of sections 20-28 of the bit-vector note, which predate sections 51-81 (memoised infer, shared shifts, hash-consing, scoped interning). The survey's options B-E (new `Expr` form, NbE, levels, arena) have no workload to justify them; for this lemma the kernel is not the bottleneck. The node-churn options note is marked superseded.

## Other lemmas re-timed at n=64 (2026-10-04)

`scripts/experiments/lemma_times.sh` (log `logs/lemma_times.out`; one run, BelowNormal, scoped interning, CPU about 55% from other sessions, Defender RTP off, GPU not used). Build and check, at n=64:

| lemma | build | check | n=128 / larger |
|---|---|---|---|
| `add x 0 = x` | 28 ms | 84 ms | n=512: 3.2 s + 9.8 s |
| `add x y = add y x` | 20 ms | 58 ms | |
| `add` associativity | 0.90 s | 1.25 s | |
| `or_disjoint` (H4) | | | n=14: 15 ms + 23 ms |
| H3 / D2 / good-add | 68 / 19 / 6 ms | 25 / 36 / 94 ms | n=128: all under 0.4 s check |

All hand-written lemmas are well under 2 s at n=64 and grow about 2x per doubling (associativity) to 4x (`add x 0`), so the stale 14-20 s figures in sections 18-29 of the bit-vector note are superseded (banner added there). **Not covered:** the rewriter-generated laws (section 82: mul 16 s build + 37 s check for 40 laws at n=64; lt 12.9 s + 20.2 s), which dominate the remaining cost; the kernel-performance thread is closed for hand-written lemmas only. Test `add_assoc_scaling_scoped` (ignored, `ASSOC_NS`) was added for this.

### Hash-cons table: pre-sizing tried, no gain (2026-10-04)

The table is already tuned (pointer-keyed `PtrMap`, a six-word `NodeKey` hash, entry API). Size at the end of the mul n=32 sweep (40 laws, one scope): 1.65M nodes, 1.26M `inst`, 0.68M `shifts`, 0.59M `uses`, 0.13M argument sets, so roughly 250 MB. Reserving 2^21/2^21/2^20/2^20 entries at activation, to avoid regrowth: process CPU time over three interleaved runs each, 24.0-26.7 s (unreserved) against 24.6-29.4 s (reserved), i.e. no difference within the noise of other sessions' load (wall times swung 8.5 s to 15.4 s build for the same exe). Reverted. The 44% self time is then probing a table that no longer fits in cache, not growth or hashing: only fewer entries would help (skip memoizing `inst`/`uses` for small nodes, or drop `uses` for shallow terms), which trades hits for misses and needs the same noisy measurement. Not pursued; the profile (default mul sweep) is the only evidence so far.

## Would a native (x86_64) backend help? Execution bench (2026-10-04)

`scripts/experiments/exec_bench.sh` (log `logs/exec_bench.out`; `benches/execution.rs --quick`, BelowNormal, CPU about 60% from other sessions, RTP off, so ranges are loose). Interpreter / JIT cold (compile + verify) / JIT warm:

| workload | interpreter | cold | warm |
|---|---|---|---|
| fib(30), non-tail | 1.68 s | 22 ms | 12.4 ms (about 9 ns per call) |
| gcd, loop | 9.7 us | 4.5 ms | 545 ns |
| factorial(10) | 9.1 us | | 654 ns |
| redundant arithmetic | 10 us | | 490 ns |
| capturing closure loop | 18.5 ms | 2.0 ms | 9.7 us |
| closure-typed loop-carried loop | 30.7 ms | 56 ms | 158 us |
| inconsistent-arity loop | 199 us | 2.6 ms | 1.17 us |

Reading: compiled code is already fast (fib about 9 ns per call, 135x the interpreter). Two costs a native backend could attack: (1) a **floor of about 0.5 us per warm call** (gcd and factorial do almost no work; native would be tens of ns), which is wasmtime entry plus `JitEngine::apply` overhead, not code quality; (2) **cold cost 2-56 ms per new term**, which matters for search that executes many fresh candidates. The split of the cold cost between wasmtime compilation and kernel verification is not measured; a backend change helps only the first part. Neither cost shows up in the current bottleneck (kernel checking of generated proofs, 53% of the mul sweep). Decision: no backend now; if execution of many fresh candidates becomes the workload, first measure the cold split (compile vs verify) and the per-call floor in `apply`, which a cheaper entry path might fix without a new backend.

### Entry-reduction estimate (not built)

Nodes carry no size field, so "skip the memo for small nodes" needs a proxy (children all leaves) checked on every call. Even if it halved `uses` (0.59M of about 4.3M entries), that is under 7% of the entries and probably under 3% of time, below the noise of the shared machine. Not worth the code until a quiet-machine baseline exists.

## Rewriter-generated laws re-timed, and profiled (2026-10-04)

(Added late: the first attempt to write this section failed silently and was found on 2026-10-04 during the proof-size work below.)

`scripts/experiments/sw3.sh` (log `logs/sw3.out`; BelowNormal, CPU 55-61% from other sessions, RTP off), the section 82 sweep (40 laws) with the current kernel:

| family | n=32 build + check | n=64 build + check | section 82, n=64 | slowest law at n=64 |
|---|---|---|---|---|
| mul | 8.4 s + 12.6 s | 26.7 s + 52.6 s | 16 s + 37 s | 6.7 s |
| lt | 3.7 s + 4.5 s | 16.0 s + 18.4 s | 12.9 s + 20.2 s | 5.4 s |

No speed-up since section 82 (1.3-1.4x worse, within what the other sessions' load explains; not re-run).

**Profile** (samply, `scripts/experiments/prof_an.py`, `logs/mul_prof.txt` transcribed from the console; the default `scaling_sweep`: mul, 30 laws, n=4..32, so the shape, not the n=64 figure): 40,740 samples. Checking (`infer_rc` and below) is 53% inclusive; `hc::intern` alone 32%. By self time: **hash-cons table 44%**, other kernel 41%, dropping `Vec<Sig>` 2.8%, rewriter/search/machine code 1.6%. The thread-local `RefCell` lookup and the table probing dominate; the rewriter is not a factor. The kernel-rework options B-E would not touch this cost.

### Proof sizes of generated laws (2026-10-04)

`scripts/experiments/proof_sizes.sh` (`logs/proof_sizes.out`; the sweep now also prints the proof DAG node count per law; same load caveats). 40 laws each:

| family | n=16 median / max | n=32 | n=64 median / max / total | n=64 time per law | time per 1000 nodes |
|---|---|---|---|---|---|
| mul | 18.5k / 62k | 34.8k / 114k | 71.9k / 231k / 3.58M | 2.0 s (26 s build + 53 s check, over 40) | 22 ms |
| lt | 7.5k / 27k | 14.3k / 53k | 31.1k / 115k / 1.37M | 0.9 s | 26 ms |
| `add x 0` (hand-written) | | | 14.2k | 0.11 s | 7.8 ms |

Proofs grow linearly in n (about 2x per doubling), so there is no blow-up with width. A generated mul law costs about 18x the hand-written lemma at the median: about 5x from proof size and about 3x from time per node (build and check together). (An earlier chat estimate of "about 100x" compared the whole 40-law sweep to one lemma and was wrong.) The 3x per node plausibly comes from the shared table: the sweep keeps one intern scope across all 40 laws (1.6M+ nodes, cache-missing; see the hash-cons section), while each hand-written scaling run starts small. Not tested; a run with one scope per law would separate the two.

### One intern scope per law: no gain (2026-10-04)

Tests the guess above that the shared table inflates the per-node cost. `SWEEP_SCOPE=law` (new, `scaling_sweep`) gives each law its own scope. Mul, 40 laws, n=32, process CPU time, interleaved, BelowNormal, CPU about 37-60% from other sessions, RTP off: shared 31.7 s and 39.2 s; per-law 49.2 s and 40.7 s. Check time 15.9/23.2 s shared against 28.4/21.6 s per-law; build about the same. So per-law scopes are no faster and probably slower (laws reuse each other's nodes, and a small scope may not reach the 3000-call warm-up before the table switches on). The guess is not supported; the 3x per-node difference to the hand-written lemma stays unexplained (candidates: larger terms with more distinct nodes per DAG node, deeper conversions in the rewriter's proofs).

### The 3x per-node cost is mostly scale (2026-10-04, from existing numbers, no new run)

Time per proof DAG node for `add x 0` (scoped runs above): n=8 3.6 us, n=64 7.9, n=128 12.2, n=256 14.6, n=512 28.4 (check only: 2.1, 5.9, 9.5, 10.8, 21.5 us). The cost per node rises with proof size even for one hand-written lemma, as expected from a hash-cons table that outgrows the cache. The generated laws (mul n=64: 22 us per node, 14.8 check-only; lt: 26 and 14.8) sit where `add x 0` sits at 400k+ nodes, although a single law has only 72k (mul median) and the sweep shares one table across 40 laws (3.6M nodes, about 1M live in a scope by the end). Interpolating `add x 0` to 72k nodes gives about 13 us per node, so scale explains about 40% of the 22 us (8 of 14 us above `add x 0` at n=64) and the table shared across the sweep the rest, **or** a real per-node difference of about 1.7x remains; this is not separated (per-law scopes did not lower it, so the table is not the whole story). Settling it needs a hand-written lemma at 72k nodes inside a 40-law-sized table. Not run.
