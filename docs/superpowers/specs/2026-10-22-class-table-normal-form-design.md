---
status: draft
---

# The learned class table as the rewriter's normal form

Date: 2026-10-22. Evidence: `docs/tier-cycle.md`, "Canonical forms: hand-coded or learned" (the options; this is c),
"A learned table of representatives: the probe", "The table with `lt` as a second sort, its proofs, and smaller keys",
"How much random testing is worth" and "A key refined by counterexamples" (runs `2026-10-22-class-table`,
`-class-table2`, `-claim-calibration`, `-key-refine`). Roadmap goal 2 ("A kernel that improves itself"); candidate 4 in
`docs/learned-vs-fixed.md`.

## Why

A table of class representatives, learned by enumeration, makes held-out laws meet with no rules. Terms over x, y, z, 0
and -1 are enumerated by size from representatives only. Each term is keyed by its values on a set of inputs and its
sort, and the first (smallest) term of a class is its representative. Each node of a law is then replaced, bottom-up, by
its class's representative. The table built to size 9 under a key of 316 learned inputs:

- meets 189-200 of 200 of each family's held-out laws at sizes 9-13 (add3, sbo3, mix3, cmp3d) and all 15 laws the ref
  library's join left at 20000 visits; the ref library at a visit budget of 1000 meets 153-198;
- does so through 3203 distinct replacements, every one proved at width 4 and kernel-checked (2820 by `add_tree_law`,
  383 by `bitwise_law_k`, about 20 ms each);
- builds in about 1.5 s, against 10.8 s for a key of every width-3 and width-4 input (4608 inputs).

The key is learned too. Starting from the 8 tuples of 0s and 1s, 16 rounds of refuting a sample of the merges it
proposes and adding a refuting input converge to those 316 inputs (52 s). The table is a learned replacement for parts
the rewriter now fixes by hand, the most load-bearing of which is the operand order (ablating `comm`: M 106 to 880,
`docs/tier-cycle.md`'s ablation table, summarised in `docs/learned-vs-fixed.md`).

## Decisions (2026-10-22)

1. **What persists: the learned key, in the repo.** A key file of about 316 inputs (a few KB) sits beside the code like
   `PROMOTED`: learned once, then frozen. Each process builds the table from it once, when first used (about 1.5 s; a
   sweep's workers are long-lived, so once per worker). A command regenerates the file (§2). Caching the built table is
   parked (`PARKED.md`, "Cache the built class table"). Rejected: refining in every process (31-52 s each); classes made
   lazily, without enumeration (a class's representative would depend on the order terms are seen).
2. **M does not count the table's proofs.** M stays the number of laws that need a whole-term machine proof. The
   distinct table replacements proved are counted apart, as a learning cost, like the proofs of mined rules.
3. **`shr1` enters the table** as a unary operator: enumerated with its ignored second operand fixed to `0`. Looked up
   by value, any `shr1(a, b)` then maps to the representative. Reopened (2026-10-23): most `shr1` replacements have no
   prover (§3). Options: (a) prove replacements over atoms, abstracting each subterm the machine refuses (a `shr1`
   node) to a fresh variable, one mechanism for every operator the machine lacks; (b) keep `shr1` and let decision 6
   drop the unprovable classes; (c) take `shr1` out of the table. Not decided.
4. **Size 9.** Larger tables (size 11 under a 64-input key: 4M classes, capped, 8.6 s) are a later measurement.
5. **Phase 1's place in `prove_eq`:** after the truth-table and per-position steps (cheap decisions), before
   `shr_mask_eq` and the join.
6. **A replacement that fails its proof in a run is not used.** The node is treated as if its class were unknown, and
   the pair is reported, for the next regeneration of the key file. The key never changes during a run. Rejected:
   adding the refuting input to the process's key mid-run (the first form of decision 1). That would change normal
   forms partway through a task, and threads that share a process would see the change at different points, so a run's
   results would depend on timing.

## Design

### 1. One module: `tests/church_bv/classes.rs`

It holds the key, the table, lookup, normalisation with plans, and the replacements' verdicts. Interface:

- `Key`: inputs per width (tuples of three values), the operator set and the size, read from and written to the key
  file.
- `Classes::get() -> &'static Classes`: the process's table, built on first use from the key file (a `OnceLock`).
- `Classes::rep(&self, t: &Term) -> Option<Term>`: the representative of `t`'s class when the table knows it and it
  differs from `t`; `None` otherwise, including for terms over a variable other than x, y, z. Pure: no proof. The twin
  filter (§6) uses it, since a filter needs no proof.
- `Classes::step(&self, job: &mut Job, n: usize, k: usize, t: &Term) -> Option<(Term, PlanRc)>`: `rep(t)` when that
  replacement has a proof (§3), with its plan, `Plan::Law(kind, t, r, args)`, or the shared `Plan::Counting` in
  counting mode.
- `Classes::normalize(&self, job: &mut Job, n: usize, k: usize, t: &Term) -> (Term, PlanRc)`: `step` at every node,
  bottom-up, with `Cong` per node and `Trans` per replacement.

Lookup computes a node's key from its children's representatives through `ValueMemo`, the evaluator the screen uses.
The built table keeps only key hash to representative; its peak memory while building is measured in build step 1 (the
probe stored 316 B of values per class, about 75 MB at 236109 classes). The probes' code
(`docs/runs/2026-10-22/patches/key_refine.patch`) is the starting point; the probes stay patches.

### 2. The key file

`tests/church_bv/class_key.txt`: a header line naming the operators in enumeration order and the size, then one input
per line (`<width> <x> <y> <z>`). A header that does not match the build's operators or size fails the process with a
message naming the regeneration command; no silent fallback. The regeneration command is an ignored test,
`classes::regenerate_key`, run like the driver's commands. It runs the refinement of run `2026-10-22-key-refine`: build,
sample 20000 merges, refute them, add one refuting input per merge not yet separated, and stop on a clean sample. Its
refuter also checks every width-3 input, which the probe's did not (merges wrong only at width 3 went unseen). The file
is written only when the loop stops on a clean sample.

### 3. Verdicts: only a proved replacement is used

A replacement `u -> r` is used only with a proof at the job's width `n` (4 in the loops, `miner.rs`'s `(n, nv, kv)`;
the probe proved all 3203 at width 4). Its verdict is decided on first use and kept in a process-wide map keyed by
`(u, r, n, k)`:

- `Bitwise` when neither side has an `add` or `sub` and their truth tables agree (`bitwise_law_k`, which takes shifts);
- else `Tree` when `tree_encoding` finds a carry encoding (already process-wide, `TREE_ENCS`);
- else unusable (decision 6), including a pair over `CARRY_CAP`.

The probe tried the encoding first and fell back to `bitwise_law_k` (`prove_checked`, then 383 carry-free pairs); the
truth table goes first here because it needs no search.

Compiling the plan's law goes through `shared_lemma` and `add_tree_law` as any `Plan::Law` does, so the lemma cache
shares its statement across a loop's processes. Counting mode decides the verdict the same way but builds no proof: it
runs the encoding search, so counting cannot claim a replacement that has no proof. That search is the cost to watch:
the probe's 20 ms each was search, proof and check together; how much is search, and how many new replacements a loop
touches, is measured in phase 1. `tree_encoding` does not take `shr1` (`Machine::parse` refuses it), so a `shr1`
replacement over `add` or `sub` has no prover: 4599 of 5265 sampled ones (`docs/tier-cycle.md`, "`shr1` in the class
table, and a table's memory"); decision 3 is reopened there.

### 4. Phase 1: a step in `prove_eq`

After the per-position step, both sides are normalised by the table. If they meet, the step returns
`Trans(pa, Sym(pb))`; if not, the cascade goes on with the original sides (`shr_mask_eq`, the join, the machine
fallback). Ablation name `classes`. This is additive and measures the table on the real loop before anything is
removed.

### 5. Phase 2: the normal form

`rewrite` applies `step` to every node it produces, children first and rule results included, before trying rules on
it. A representative is a fixpoint of the table, so rules then act only on nodes the table does not know (larger than
its size, over a fourth variable, or with an unusable replacement). Then each fixed part the table may subsume is
ablated by its existing switch (`ABLATE=...`), and deleted with what only it used when removing it costs nothing on the
gate:

- the operand order (`comm`, by `show()` text);
- the built-in `add` steps (`assoc`, `tree`, `chain`);
- the promoted rules (`promoted`);
- the truth-table and per-position steps of `prove_eq` (`eq_truth`, `eq_pos`).

A part that still pays is kept, with the measurement recorded in `docs/learned-vs-fixed.md`.

### 6. `ClassReps` is replaced

The law generator's twin filter (`search::ClassReps`) is a smaller, hand-built class table, keyed on every width-4
input, over leaves, two-leaf terms and a family pool's subterms. It moves onto `Classes::rep`; its twin key (renamings,
sides normalised below their roots, the root kept) stays. What the move loses: classes among pool subterms larger than
the table's size, and `ClassReps`'s fallback to a child of equal value (`add(t, 0)` to `t`) for nodes it does not know.
Nodes within size 9 lose neither. Twins found change, so the generator stage is measured again on cold loops before and
after (`docs/tier-cycle.md`, "The law generator on ref mines and warm loops").

### 7. Phase 3: mining on what is left

Mines see the laws normalised by the table, so mined rules target only what it leaves. Measured: rules mined, M, and
the frontier (`ROADMAP.md`, v0.5) by law size.

### 8. Counts

`m.tsv` gains a column, the distinct table replacements proved in the batch (decision 2). Serve logs report the table's
build time and size once per process, and any unusable replacement.

## Testing

- **Key file:** a written and re-read key is equal; a header with another operator set or size fails with the
  regeneration message.
- **Table:** built from the key file to size 5, it maps `sub(y, y)` to `0`, `add(x, 0)` to `x`, `xor(x, -1)` and
  `sub(-1, x)` to one representative (the cases of `ClassReps`'s test), and `shr1(x, y)` to `shr1(x, 0)`.
- **Proofs:** every replacement the size-9 table uses on the held-out sets of run `2026-10-22-key-refine` has a
  verdict, and its plan compiles and kernel-checks (an ignored test, run at each phase).
- **Counting and compiling agree:** a law closed by the step in counting mode compiles to a checked proof.
- **Phase 1:** the step closes a law the join needs today, and `ABLATE=classes` restores the old answers.
- **Gate, per phase:** `docs/runs/2026-10-18/scripts/salts_ab.sh` (cold:cmp3d, A/B per salt; salts 1-5): M, rule
  agreement, job CPU and wall; then the held-out sets and the sweep's own M on salts 1-10 for phase 2's ablations.

## Build order

1. `classes.rs`: key file, table (with `shr1`), `rep`, verdicts and `regenerate_key`; generate the key file; the
   size-5 tests; the `shr1` verdicts and peak memory measured.
2. Replace `ClassReps` with it; measure the generator stage.
3. Phase 1 in `prove_eq`; the gate.
4. Phase 2 in `rewrite`; the gate; then one ablation at a time, each gated, deleting what costs nothing.
5. Phase 3: the miner on the residue; M and the frontier.

Each step ends with `docs/tier-cycle.md` and `docs/learned-vs-fixed.md` updated.

## Risks

- **Counting-mode verdicts may be slow.** Each new replacement runs an encoding search; if loops touch thousands, the
  step costs more than the joins it saves. Phase 1's gate shows it (job CPU).
- **Memory per worker.** Every worker holds its own table: one build with `shr1` commits 257 MB (`docs/tier-cycle.md`,
  "`shr1` in the class table, and a table's memory"), and a sweep runs several workers per lane.
- **The key is not exact.** A clean sample of 20000 bounds wrong merges to a few in 20000 (at 95%); a wrong merge costs
  a failed verdict and that class's coverage (decision 6), never soundness.
- **Laws beyond the table's range** (more variables, larger roots) still need rules and the join; how much of a law's
  bulk the table normalises at larger sizes is measured, not assumed.
- **Normal forms change.** Mined rules, preferences and the promoted rules were learned under the old normal form; the
  gate's M compares whole loops, which re-mine, so rules will differ between arms.

## Not in scope

- The belief layer (`ROADMAP.md`, goal 3).
- Tables over more than three variables, or beyond size 9.
- Caching the built table (parked, decision 1).
- Postulates in the kernel.
