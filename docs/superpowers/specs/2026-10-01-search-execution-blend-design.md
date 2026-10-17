---
status: active
---

# Proof search blended with execution (exploration note, 2026-10-01)

Status: **explored and partly built (test code only; `src/kernel.rs` untouched); section 0 is the current state.** Goal from the user: with lemmas ablated from the library, AI proof search should find the missing lemmas; search should run concurrently with execution and use what execution reveals; blend the phases (run / check / search) as far as is useful.

## 0. Current state (read this first; details in the numbered sections)

(Sections 37 onward live in `2026-10-02-search-execution-blend-design-part2.md`; the table below cites sections in both files.)

**Fresh sessions: read `2026-10-04-research-state.md` first** (the proposer line, sections 66-90 compressed). Since it was written: the loop between permutative and regrouping rules is settled as a trade-off, not a bug (section 89: `PERM_ORDER=lpo` gives unique normal forms at a cost of 8 to 68 machine-free laws, and is no more confluent than the default on the benchmark law sets); the shr bit-0 leftovers are reachable by rules stated over normal forms (section 90a).

`src/kernel.rs` is untouched; everything below is in `tests/church_bv.rs`. Pipeline: a **pool** of small terms over `Term` ops
(add, and, or, xor, sub, lt at the root, shl1, shr1) gives candidate laws by equal value at width 4 (`pool_conjectures`); each law is
proved at every width by (1) the **rewriter** (`rewrite`, built-in `rules()` plus mined `EXTRA_RULES`, ordered by `rule_order_ok`),
(2) **bitwise/position provers** (`bitwise_law_k`, `PosTerm`) for add-free terms, (3) the **mask reduction** `shr_mask_eq` for right
shifts, and (4) the **machine proof** `add_tree_law` (Moore-refinement encoding search over bit-serial carry machines) as the
fallback. Every proof is kernel-checked in tests. The **rule miner** (`rule_miner`, `scripts/miner_summary.sh`) takes the laws that
still needed a whole-term machine proof ("stragglers") and learns rewrite rules that remove them.

| Family | Laws | Unproved | Stragglers | Covered by mined rules | Section |
|---|---|---|---|---|---|
| mul by constants (MAX=12, full) | 246 | 0 | 40 (206 machine-free) | built-in rules | 44 |
| mul (MAX=5) | 50 | 0 | 0 after promotion (4 before) | promoted | 45, 50, 60 |
| shl | 305 | 0 | 5 after promotion (23 before) | 0 more | 41, 50, 60 |
| lt | 150 | 0 | 7 after promotion (26 before) | 0 more | 43, 50, 60 |
| shr (`DEEP=1 MINER_SUB=1 STRIDE=3`) | 900 | 0 | 76 after promoting the mul/shl/lt rules (79 before) | 33 more (the same 43 stay uncovered: carry-reasoning or constant-1 laws); its 15 useful rules are promoted too, not re-measured | 48-50, 60 |

Lemma ablation (section 51): the library's add lemmas are re-proved from their statements alone. Ablating the rewriter's own
lemmas under the miner: `assoc` mostly recovered, `collapse` partly, `comm` not (an ordering decision, not a rule), `zero`/`not`
redundant (section 45). Blame localisation needs no kernel holes: the kernel has none, and builder-level blame is what the miner does (section 62).

**Added since the table (sections 52-63).** Mined rules are promoted into the library (`PROMOTED`, 35 rules, `ABLATE=promoted` removes them; section 60):
one promotion round fixes most stragglers in mul, shl and lt and makes the shr mining about 50x cheaper; a second round finds nothing for shl and lt. Variable
multiplication exists as a circuit with per-width case-analysis laws (commutativity, constants, distributivity, associativity; n = 2-4, sections 58-59), not uniform in n.
The borrow-bit form does not remove the machine proof of the 7 `lt` stragglers (section 61). Candidate scoring runs on `RULEMINER_THREADS` workers, 3.6x at 8 threads
with identical output (section 63).

**Open.** The 43 shr and 7 `lt` stragglers are carry facts (a new proof technique, not more rules); goal D (laws uniform in the width) is blocked by the missing
induction principle for Church encodings (sections 53-57); a model proposer (section 4 option D) is unbuilt and its target is now the families closed by hand rules plus 1-3 mined rules (section 75), so a model would have to beat that; sections 76-81 add the scaling check of the final rule sets, rule transfer, and a rule language model (Burn, `tools/rulelm`) that covers 8 of 64 stragglers against the miner's 51 in every variant tried (scripts and raw logs: `scripts/experiments/README.md`); sections 66-71 built the harness, a rule corpus and the `add3` benchmarks (the deeper one leaves 23 of 64 uncovered by the miner, no answer key) and found a heuristic baseline (`goal`) the model must beat; the search-alongside-execution channel
(section 6, question 4) is unbuilt too. Tooling: `scripts/miner_summary.sh` (families; `FAMILIES=shr` was the 10-minute one before promotion), `RULEMINER_*`/`ABLATE` env vars
(sections 36-45, 63). Long runs: BelowNormal, at most 12 threads.

## 1. What `../renno` offers (read from code; spot-checked: `Cont::append` at cont.rs:114, `Builtin::Fail` panics at machine.rs:676, `desugar_refinement` at parser.rs:1285)

| Idea in renno | Fact | Use for tatic |
|---|---|---|
| Multi-shot continuations | Persistent linked list of frames; capture clones the frames up to the handler (O(frames)); resume copies the continuation's spine onto the tail (O(len k)); contents shared via `Rc`. `choose` works as an ordinary handler. | Search as an effect: a branch point captures the state, each candidate lemma resumes it. Cost per branch is the stack depth, not the heap. |
| Gradual verification | Decided in the parser: constant-fold the predicate on a closed Int, else wrap `if pred then body else fail`. No symbolic prover, no "unknown" result; failure is silent fallback to a runtime check. | The three-way shape (proved / checked at run time / unknown) is the right interface; renno's prover is too weak to borrow, and `fail` is a Rust `panic!`, not a handleable effect. |
| Separation | Pipeline is strictly parse, check, run. Nothing at run time feeds back into static decisions. No traces, no search, no speculation. | Nothing to reuse here; the blending is new work. |
| Hooks | Effect handlers and a builtin table (pure Rust, cannot capture `k`). `Rc`-based, not `Send`. | An external prover would be a handler or a serialized message, not a thread sharing the interpreter. |

Net: renno gives a good *execution substrate* for search (cheap multi-shot) and a good *vocabulary* (static / dynamic / unknown), not a prover or a feedback loop.

## 2. What tatic already has to build on

- A kernel that is a fast, trustworthy judge: whole-lemma checks cost 10-300 ms at n up to 128 (design doc sections 87-89), failing statements are rejected quickly (section 83).
- Generator-built proofs per width, which are templates: `add x 0 = x`, commutativity, H3, D1, D2, `good_add` all follow "eliminate the witnesses, rewrite per bit, `cong_n`". A search that proposes a *statement* and instantiates a *template* is much smaller than free-form term search.
- Cheap refutation by computation: `def_eq` on literals decides a candidate on concrete values (section 85 test style), the analogue of renno's runtime check.
- Known walls a search must respect (all in doc sections 86-89): no cumulativity, so witnesses eliminate only into the right universe; no eta; `true = false` is not refutable (section 88); unary `Nat` does not scale (section 89). A candidate that needs one of these should be rejected early with that reason, not searched.

## 3. Where the phases can blend

| Phase | Today | Blended form |
|---|---|---|
| Run | `def_eq`/`normalize` on literals | Same, but each run is a *probe*: log which sub-terms were compared and which differed. |
| Check | kernel `check` of a finished proof | Check a *partial* proof: holes as postulates (`Postulates` scopes already exist), so the kernel reports the type of each hole, which is the subgoal. |
| Search | none | Proposes statements and templates; filters by running them first; only survivors reach the kernel. |

Concrete feedback channels from execution to search (each is cheap, none is built):
1. **Counterexample pruning.** Evaluate a candidate lemma on sampled literals (n=4 exhaustively, n=32/64 sampled); reject on any mismatch before building a proof. This is renno's runtime check applied to conjectures.
2. **Conjecture mining.** Run the library's operations on pairs of literals and group results that coincide (`add x 0` vs `x`, `add x y` vs `add y x`), proposing the equalities that survive as lemma statements. Ablating `add x 0 = x` then means the miner should rediscover it.
3. **Blame localisation.** When a downstream theorem fails to check, the kernel's error plus the hole type names the missing fact; the failing sub-term is the search target.
4. **Concurrency.** Checks are independent and pure per query, so a worker pool over candidates is natural (the kernel is thread-local state, `InternScope` per thread). Cap at 12 busy threads (LONG_RUNS); the tatic kernel is not shared across threads, each worker builds its own terms.

## 4. Approaches, with pros and cons

| Option | Pros | Cons |
|---|---|---|
| A. Conjecture miner + template instantiation + kernel as judge (recommended first) | Smallest; every part exists or is small; the kernel is the only trusted piece; ablation is easy to define; no ML needed to start | Finds only lemmas that fit an existing template; new proof shapes (like the eta repair of section 87) need hand-written templates |
| B. Hole-driven search: partial proofs, subgoals from hole types, tactics proposing terms | Reaches new proof shapes; matches how the failures actually arose | Needs a tactic layer and goal management that tatic lacks; larger |
| C. Search as an effect on a renno-like machine (multi-shot) | Backtracking and sharing for free in that substrate | Requires running the proof builder inside renno or porting its machine; two codebases |
| D. Learned model proposes statements/terms; kernel checks | Most general | Needs data, an interface, and an evaluation; premature before A shows what the search space looks like |

## 5. Ablation protocol (proposal)

An *ablation* removes one library lemma (for example `add_zero_proof`) and keeps everything that depended on it as a goal. Success: the search emits a proof that the kernel accepts for the *statement* of the removed lemma, within a time budget, without seeing its proof. Score by: found / not found, kernel-check count, wall time, and whether the found statement is the original or a stronger one. Start with the lemmas of `tests/church_bv.rs` (about ten), each already having a generator, so the template exists but is hidden from the search.

## 6. Open questions

1. Is the search allowed to see proof *templates* (the shapes), or only the kernel's primitives? This decides whether option A is a fair test of "rediscovering" a lemma.
2. What is the unit of "execution" to learn from: `def_eq` on literals, whole-library runs, or the compiled programs the bit-vector library will be used on (the allocator, closure packing)?
3. How should unknown-because-of-a-wall (section 3 of this note) be reported: as a rejected candidate with the reason, so the search learns the wall?
4. Concurrency target: many candidate checks in parallel (easy), or search running alongside a long-running execution and consuming its observations (needs a trace format; none exists in tatic or renno).

## 7. Suggested first step (needs your go-ahead)

Option A at n=4: a test that enumerates candidate equalities over the bit operations by evaluation on all 4-bit pairs, keeps the surviving ones, and for each tries the matching generator template; report which known lemmas are rediscovered. It would reuse `lit`, `def_eq`, and the existing proof builders, add no kernel code, and give the first real data on the search space.

## 8. First experiment: the conjecture miner at n=4 (2026-10-01)

Decisions on the open questions (user: "templates: not sure; execution: anything available, the line should not be clear; walls: not sure"):
- **Templates**: run both arms and compare, rather than choose. The first experiment is the template arm (conjectures matched to the existing generators); the no-template arm is the next one.
- **Execution**: not delimited. The miner uses the kernel for both running terms (`normalize` on literals) and judging (`check` of a template proof); the same loop will take any other observation that becomes available.
- **Walls**: logged with the reason for now, not fed back into the search.

`conjecture_miner` (`tests/church_bv.rs`, ignored; `MINER_N` sets the width): 68 terms (leaves `x, y, 0, -1` and each of add/and/or/xor over two leaves), each run on all 256 pairs of 4-bit literals through the kernel, fingerprinted by normal form: 15 behaviour classes in 0.38 s, 53 equality conjectures. CPU load 27%, Defender real-time protection off.
- **Rediscovered with a working template**: `add x 0 = x`, `add 0 x = x`, `add x y = add y x` (their proofs from `add_zero_proof`, `add_identity_proof`, `add_comm_proof` check at n=4).
- **Mined, no template in the library** (so no proof is attempted): commutativity of and/or/xor, idempotence (`and x x = x`, `or x x = x`), `xor x x = 0`, absorbing and identity laws (`or x -1 = -1`, `and x 0 = 0`, `and x -1 = x`, `xor x 0 = x`), and `add x -1 = add -1 x`. These are the candidates for the no-template arm.
- **Not mined (honestly)**: anything needing a hypothesis or more than two variables (associativity, `sub`, the `GoodBv`-conditional lemmas of section 87) because terms are one operator deep over two variables. Next widening: depth 2, three variables.
- The miner proposes statements; fingerprint equality on 256 pairs is a refutation filter, not a proof. A conjecture is a lemma only when the kernel accepts a proof.

## 9. No-template arm and a wider miner (2026-10-01)

`bitwise_law(n, t1, t2)` (`tests/church_bv.rs`) proves `t1(x, y) = t2(x, y)` for any terms built from and/or/xor, 0 and -1 over two good vectors, with no lemma-specific template: per bit, case analysis on the two `GoodBool` witnesses with `refl` leaves, then `cong_n` and the two witness eliminations. The kernel decides every leaf, so a false law fails to check (`bitwise_law_proves_true_laws_and_rejects_false_ones`: four true laws proved at n=1,2,4, two false ones rejected). It shares `lemma2` and the proof skeleton of `add_comm_proof` but contains nothing about any particular law.

`conjecture_miner` (ignored; `MINER_N`, `MINER_VARS`, `MINER_DEEP=1`) now classifies every conjecture. CPU load 39%, Defender real-time protection off.

| config | terms | classes | conjectures | proved by `bitwise_law` | rejected | need `add` | use a 3rd variable | mining time |
|---|---|---|---|---|---|---|---|---|
| n=4, 2 vars, depth 1 | 68 | 15 | 53 | 43 | 0 | 10 | 0 | 0.55 s |
| n=4, 2 vars, depth 2 | 2116 | 87 | 2029 | 1188 | 0 | 841 | 0 | 29.9 s |
| n=3, 3 vars, depth 2 | 4105 | 234 | 3871 | 1188 (same x,y subset) | 0 | 841 | 1842 | 64.3 s |

Reading:
- **Templates are not needed for bitwise laws.** Every bitwise conjecture the miner produced was proved by the one generic builder (1188 of 1188, none rejected), including laws absent from the library (commutativity and idempotence of and/or/xor, absorption `and x (or x y) = x`, `xor x x = 0`, De Morgan-style identities with -1). Proving all 1188 took 1.7 s.
- **`add` is the gap.** All conjectures that mention `add` (10 / 841) are unproved. The three known ones have hand-written templates. Most of the rest are *instances* of those three under bitwise congruence (`xor(add(x, y), y) = xor(add(y, x), y)` is `add x y = add y x` inside `xor`), so a rewrite step that applies a proven lemma under a context would discharge most of them; that is a different mechanism from a template, and the next thing to test. The ones that are not instances (associativity, `add x -1`) need carry reasoning with a new template.
- **Associativity is conjectured** at n=3 with three variables (`MINER add associativity conjectured: true`), but it is not proved: the builder takes two variables and no `add`, and fingerprint equality at n=3 is not a statement about n=32.
- **Cost of "execution".** Fingerprinting by `normalize` through the kernel dominates (30 s and 64 s); proving is cheap (1.5-1.7 s for over a thousand proofs). A cache of normal forms keyed by (term, inputs), or fingerprinting on a subset of inputs first, would cut it; not done.
- **Walls** reported by the run: none triggered for bitwise laws. For `add` laws the wall is the missing template, not a kernel limit.

## 10. Rewriting with proven lemmas (2026-10-01)

`rewrite_law` in `tests/church_bv.rs` proves an `add` conjecture from the three library lemmas
(`add a 0 = a`, `add 0 a = a`, `add a b = add b a`), with no new template:

1. `rewrite` simplifies both sides bottom-up. Each step is `cong_n` on the enclosing operator (all four are
   closed terms) chained with `trans_proof`; commutativity orders the operands of `add` by `show`.
2. `prove_eq` closes the rewritten pair: `refl`; or `bitwise_law` over *atoms* (each variable and each `add`
   subterm becomes one of two variables, instantiated at the atoms' values and witnesses; guarded by a
   four-row truth table so the kernel check cannot fail); or, for two sums, `cong_n` on proofs of their operands.

Result at n=4, two variables, two operators deep (2029 conjectures, CPU 12-32%, Defender RTP off):

| step | proved | remaining |
|---|---|---|
| `bitwise_law` (section 9) | 1188 | 841 mention `add` |
| + identity/commutativity rewriting, atoms with `bitwise_law` (first version) | 553 of 841 | 288 failed to check |
| + truth-table guard and operand recursion | **719 of 841**, 0 failed checks | 122 |

The 288 kernel rejections of the first version were not unsoundness: different `add` operands made the atom
abstraction a false law, and the kernel refused each. The guard moves that decision before the build.

The 122 left, from the printed sample, are of two kinds: (a) nested sums (`add (add x y) y = add x (add y y)`),
which need associativity, and (b) a bitwise-constant operand inside a sum (`y = add (or 0 0) y`), which a
bitwise normal form for operands would close (`or 0 0 = 0` by `bitwise_law`, then `cong_n`). (b) is cheap;
(a) needs a carry-reasoning lemma. The split was not counted.

Regression test: `rewrite_law_proves_add_conjectures_from_the_library_lemmas` (three provable laws, one false
law and one associativity instance returning `None`). Suite: 15 passed, 24 ignored.

### Items parked from the last step list

- **Associativity / `add x -1` template.** Needs a three-variable builder: carries of `add (add x y) z` and
  `add x (add y z)` agree bitwise by a carry-propagation invariant, and `add x -1` is a borrow chain. Do it after
  (b) above so the count of conjectures that truly need it is known.
- **Cache normal forms.** The miner spends 20-30 s in `normalize` of every term on every input tuple. Key by
  (term, inputs), or fingerprint on a subset of inputs first and confirm survivors. Blocks wider miners (n=4
  with three variables is 2^12 tuples per term).

## 11. Bitwise-operand collapse, normal-form cache, associativity (2026-10-01)

Three steps on the section 10 list; all in `tests/church_bv.rs`. Same configuration (n=4, two variables, two
operators deep, 2029 conjectures; CPU 16-23%, Defender RTP off, BelowNormal).

| step | add conjectures proved (of 841) | left |
|---|---|---|
| section 10 | 719 | 122 |
| + a bitwise node equal to 0, -1 or one of its atoms collapses to it (truth table, then `bitwise_law`) | 807 | 34 |
| + associativity as a rewrite rule (right-nest sums, then sort, re-rewriting after each step) | **833** | 8 |

0 kernel rejections throughout. The 8 left are all `add (xor x -1) x = -1` (and its operand-order variants),
i.e. x + ~x = -1: a single carry that stays false, a borrow-chain lemma, not associativity.

**Normal-form cache.** `nf_cached` memoizes the normal form per (subterm, input tuple) and builds each term
from its operands' normal forms. Classes are identical (2116 terms, 87 classes, 2029 conjectures). Run time
20.4 s to 13.4 s at n=4 with two variables, and 64 s to 41 s at n=3 with three. A modest gain: `normalize` on
the operator applications still dominates, so wider miners need fewer evaluations (fewer tuples), not only memoization.

**Associativity (`add_assoc_proof`).** The two sides carry separate states, (c, d) and (e, f). Only the total
matters (c + d = e + f), encoded as the pair (xor c d, and c d); no hypothesis about `true = false` is needed.
Six closed lemmas (`lemma_n`, a k-variable case analysis with `refl` leaves) say each side's output bit and next
pair equals a fixed table of (a, b, z, xor, and); `cong_n` on the two carried equalities links the sides, bit by
bit. `GoodBool` witnesses for the symbolic carries are composed with `good2`. Checks at n=1, 2, 4; the wrong
statement (`add x (add y y)`) is rejected. Test: `add_is_associative_on_symbolic_good_vectors`.
Rewrite rules: `(p+q)+r -> p+(q+r)`, and `a+(b+c) -> b+(a+c)` when `b` sorts before `a`.

Cost: the miner's rewrite pass went from about 6 s to about 70 s because `add_assoc_proof` and the witnesses are
rebuilt at every rule use (not cached). Correct, not yet cheap.

Caveat: `lemma_n`, `table_expr` and the total-carry encoding are generic enough to reuse; the invariant itself
is hand-derived (the search did not find it). It is the first concrete candidate for the ablation protocol
(section 5): remove it and see whether anything finds the (xor, and) encoding.

## 12. Cache, x + ~x, full coverage, first ablation table (2026-10-01)

**Closed-term cache.** `memo` builds each closed lemma proof or witness once per key and width (`good_add`,
the bitwise witnesses, the identity, commutativity, associativity and x + ~x proofs). The miner's rewrite pass
went from about 70 s to about 20 s (the whole conjecture loop, 1188 bitwise plus 841 `add` proofs).

**`add x (xor x -1) = -1`** (`add_not_proof`, test `add_of_x_and_not_x_is_all_ones`, n up to 8, the wrong
statement rejected). Same carry-stays-false pattern as `add_identity_proof`, with a bitwise second operand.
Two rewriter additions go with it: commutative bitwise operands are put in a fixed order (constants last, by the
generic bitwise law), and a commuted form of the x + ~x rule.

**Coverage: 841 of 841 `add` conjectures proved at n=4, two variables, two operators deep, 0 kernel rejections.**
(Together with the 1188 bitwise ones: all 2029 conjectures.)

**First ablation table.** `ABLATE=<rule>` switches one rewriter rule off (`zero` = both identities, `comm`,
`assoc` = both nesting rules, `not`, `collapse` = bitwise node collapse). Conjectures left unproved of 841
(CPU 39%, Defender RTP off, BelowNormal):

| ablated | left | what the search would have to supply |
|---|---|---|
| none | 0 | |
| `zero` | 389 | `add x 0 = x`, `add 0 x = x` |
| `comm` | 197 | `add x y = add y x` (also disables the rules that use it) |
| `collapse` | 86 | bitwise simplification inside sums (not a library lemma: derived by `bitwise_law`) |
| `assoc` | 26 | associativity (the (xor, and) total-carry invariant) |
| `not` | 8 | x + ~x = -1 |

The ablated runs have 0 failed checks: a missing rule never produces a wrong proof, only an unproved conjecture.
So the left-over set after an ablation is exactly the target list for a proposer, and "found the lemma" is
checkable as "the left-over count drops back to 0".

**What this is not.** No search exists yet: the rules are fixed code, and the ablation only shows which lemma
each conjecture needs. The closest thing to a proposer is the miner (statements) plus the generic builders
(`bitwise_law`, `lemma_n`); the missing part is finding a *proof invariant* such as (xor c d, and c d), which
here was derived by hand. The smallest honest next experiment is to ablate `not` (8 conjectures, a one-carry
invariant: "carry stays false") and have a generic carry-chain builder, given only the statement and
the hint "track a simpler expression for the carry", discover it.

## 13. A builder that discovers the invariant: constant carry (2026-10-01)

`carry_chain_law` (tests/church_bv.rs) proves `add A B = T` for bitwise `A`, `B`, `T` over x, y from the
statement alone. `find_constant_carry` is the discovery step: it looks for a constant carry value R that is
(a) the initial value (so only `false` qualifies), (b) inductive: `carry(A_bit, B_bit, R) = R` on all four bit
pairs, and (c) under which every sum bit equals the target bit; all decided by truth table (`normalize`)
before anything is built. The proof is then the `add_identity_proof` pattern generalized: two `lemma2` per-bit
lemmas, `cong1` to rewrite each carry to R, `cong_n` over the bits. `bitwise_law` was refactored around a shared
skeleton, `two_var_law`, so both builders reuse the witness eliminations.

Ablation results (n=4, two variables, two operators deep; CPU 26%, Defender RTP off, BelowNormal; the builder is
tried on every conjecture the rewriter leaves unproved, in both orientations):

| ablated | left without the builder | recovered by the builder | left with it |
|---|---|---|---|
| `not` | 8 | 8 | **0** |
| `zero` | 389 | 175 | 214 |
| `not,zero` | | 183 | 214 |

So the one-carry invariant is found, not given: with `not` removed the builder rediscovers x + ~x = -1
(and the operand-order variants) and the left-over count returns to 0, which is the success criterion of
section 12. It also recovers 175 of the 389 conjectures left by removing the zero identities, since
`add x 0 = x` and `add 0 x = x` are themselves constant-carry laws.

The 214 left under `zero` are conjectures with a nested sum (for example `add (add x 0) y`), outside the
builder's scope (it needs add-free operands).

**Honest limits.** The "search" is a decision over two candidates (R = false or true, and only false can start
the chain); the invariant family is constants only. It does not find the associativity invariant
(xor c d, and c d), whose candidates are expressions over several carries. The next rung is a search over
small carry-state *functions* (expressions in a fixed grammar over the live carries), checked by the same
truth-table test; that would have to find (xor, and) when `assoc` is ablated.

## 14. Searching the carry-state encoding; chain as a rewrite rule; sampled fingerprints (2026-10-01)

Three steps, all in `tests/church_bv.rs`. Runs: n=4, two variables, two operators deep unless stated; Defender RTP
off, BelowNormal; CPU 26-67% (other sessions' load varies between runs, so the timings are indicative).

**1. State-encoding search (`find_state_encoding`, `add_tree_law`).** A sum of three leaves (`add (add u v) w`
or `add u (add v w)`, leaves x, y, 0 or -1) is a two-carry machine. `find_state_encoding` enumerates all 16 x 16
encodings phi = (phi1, phi2) of the carry pair (c, d) and keeps one under which, for both sides, the output bit and
the next phi-values are functions of (x bit, y bit, phi(c, d)), the *same* functions on both sides (decided on
tables precomputed once with `normalize`: 16 assignments x 2 machines). The proof is the associativity proof with
the discovered phi in place of (xor, and): six `lemma_n` case analyses with `refl` leaves, `cong_n` between the
sides, the `two_var_law` skeleton for the witnesses.

Found for the tested laws: phi1 = nor(c, d) (the total is 0), phi2 = xor(c, d), i.e. the total
c + d in {0, 1, 2} encoded as (1,0), (0,1), (0,0): a different but equivalent encoding from the hand-derived
(xor, and). A false law has no encoding (test `state_encoding_search_proves_three_leaf_sum_laws`, n=1,2,4).

| ablated | left before the search | proved by the search | left |
|---|---|---|---|
| `assoc` | 26 | 26 | **0** |
| `assoc,comm` | 203 | 44 | 159 |

The success criterion of section 12 is met for associativity: with the hand-written associativity lemma removed,
the left-over count returns to 0 and nothing in the proof comes from the removed lemma. With `comm` also removed the
search covers only conjectures that are pure three-leaf sums on both sides; the rest need operand ordering.

**2. The constant-carry builder as a rewrite rule (`chain_step`, ablation name `chain`).** At every `add` node
with atom-abstractable operands, if a constant carry reduces the sum to 0, -1 or one of its atoms, rewrite to it
(instance of `carry_chain_law` at the atoms' values and witnesses). It subsumes the two identities and
x + ~x, and applies at nested positions. Ablation:

| ablated | left (fallback builder only) | left with the rule on |
|---|---|---|
| `zero` | 214 (builder not in the rewriter) | **0** (821 by rewriting, 20 by the fallback) |
| `not,chain` | 8 (all recovered by the fallback builder) | n/a |
| `zero,not,chain` | 214 | n/a (this row is the rule switched off; `zero,not` with the rule on was not run) |

So the 214 conjectures with a nested sum are closed by running the builder inside the rewriter.

**3. Sampled fingerprints (`MINER_SAMPLE`).** Fingerprint on a fixed pseudo-random subset of input tuples (plus
all-0 and all-1), not all. A class may then contain a false equality, which no proof builder or kernel check
accepts; so the kernel stays the arbiter. n=3, three variables: 41 s down to 5.9 s with the identical
4105 terms / 234 classes / 3871 conjectures. n=4 with three variables (4096 tuples per term, not feasible with
full fingerprints) in 17 s: also 234 classes. 3871 conjectures are mined, but none over a third variable is proved
yet: the rewriter, `bitwise_law` and the builders are two-variable (x, y) frameworks, so those 1842 count as
"use a third variable".

**Next.** Make the rewriter and `two_var_law` k-variable (context [x1..xk, g1..gk]); then the three-variable
associativity conjecture itself, mined at n=4, is proved with the discovered encoding, which ties items 1 and 3
together. After that, grow the encoding search beyond three-leaf sums (more carries, or a grammar of encodings
over three or more carries) and check it against the ablation of `assoc` on larger trees.

## 15. k variables and a general encoding search

Measured with the sampled miner (n=4, `MINER_SAMPLE=64`), machine CPU 28% (idle-ish), Defender real-time
protection off. Code in `tests/church_bv.rs`.

**1. k-variable skeleton.** `two_var_law` is now a wrapper over `k_var_law(n, k, ..)` (witness elimination over k
vectors); `bitwise_law_k`, `rewrite_law(n, k, ..)`, atom abstraction, truth-table guards and the collapse rule all
take their variable count from the `goods` list. The two-variable runs are unchanged (841 of 841). Test
`laws_over_three_vectors_check_and_false_ones_fail` (xor associativity, add associativity and
commutativity+associativity over x, y, z, and a non-law rejected).

**2. Three-variable miner.** All 1842 conjectures over a third variable are proved (0 unproved, 0 kernel
rejections), including associativity itself; 56 s for the proof pass.

**3. General encoding search (`Machine`, `add_tree_law(n, k, ..)`).** A sum tree whose leaves are any add-free
bitwise terms over k vectors, with c <= 3 carries (one per `add` node) and an encoding of at most two bits
(`min(c, 2)`; a total carry up to 3 fits). The same encoding is searched for both sides, which must have the same
number of `add` nodes. Tests (`state_encoding_search_handles_bitwise_leaves_three_vectors_and_four_leaves`, n=1,2,4):
`and(x,y) + or(x,y) = x + y` (bitwise leaves), associativity over x, y, z, a four-leaf reassociation, and false
laws rejected. Limit: 256^m tables, so c <= 3; five leaves would need a three-bit total and a smarter search.

**4. Ablation, n=4:**

| ablated | vars | `add` conjectures left after rewriter | proved by search | left |
|---|---|---|---|---|
| `assoc` | 2 | 26 | 26 | 0 |
| `assoc` | 3 | 26 (+1842 third-variable, all proved) | 26 | 0 |
| `assoc,comm` | 2 | 203 | 125 | 78 |
| `assoc,comm` | 3 | same 78, plus 114 third-variable | 125 | 78 + 114 |

`assoc,comm` improved from 159 left to 78. What remains is not the sum-tree shape: it is `add` nested under a
bitwise operation, e.g. `and(add(x,y), y) = and(add(y,x), y)`, `or(add(y,-1), y) = or(add(-1,y), y)`, and sums
with different `add` counts (`add(y,-1) = add(-1, add(y,0))`). Both need congruence under bitwise operators and
per-side encodings; neither is done.

**Next.** (a) Congruence through bitwise nodes: rewrite an `add` atom with a proof it equals another value, then
use the generic bitwise law with the pair as atoms. (b) Per-side encodings for trees with different carry counts.
(c) A smarter encoding search for c >= 4, e.g. enumerate the total-carry encoding family rather than all tables.

## 16. Add under bitwise operators, unequal carry counts, the total-carry family

Sampled miner, n=4, `MINER_SAMPLE=64`; machine CPU 70% (other jobs running), Defender real-time protection off.

**1. `prove_eq` closes more pairs.** (a) Equal bitwise operators: congruence on the operands, recursively (so
`and(add(x,y), y) = and(add(y,x), y)` reduces to `add(x,y) = add(y,x)` and `y = y`). (b) Two sums that operand-wise
congruence cannot close: `add_tree_law` instantiated at the variables' values and witnesses (no atom abstraction,
so no two-atom cap).

**2. Per-side encodings.** `Encoding.phi` is now one table set per side, so the two machines may have different
carry counts. `try_encoding` checks a given pair of encodings against both machines' (kernel-evaluated) transition
tables.

**3. The total-carry family (`total_carry_encoding`).** For any sum tree, sum of leaf bits + total carry = output +
2 * next total carry, so the number of set carries, in binary, is a valid state for every shape. It is tried when
the table search (equal counts, c <= 3) does not apply or fails, per side, for up to 5 carries. This is supplied by
me, not discovered: section 14's search found a different 2-bit coding (nor, xor) for three leaves, which is the same
quantity under another coding; the family is what that result generalizes to. Tests:
`total_carry_encoding_handles_unequal_carry_counts_and_five_leaves` (`y + -1 = -1 + (y + 0)`; five leaves, four
carries; false laws rejected; n=1,2,4, 33 s, dominated by the five-leaf proof).

**4. Ablation, n=4** (`needs add` = left after rewriter and all builders):

| ablated | vars | left (section 15) | left now |
|---|---|---|---|
| none | 3 | 0 | 0 (1842 third-variable proved) |
| `assoc,comm` | 2 | 78 | **0** |
| `assoc,comm` | 3 | 78 + 114 third-variable | **0** |
| `assoc,comm,zero` | 2 | not run | 0 (821 by rewriting, 20 by the chain builder) |
| `assoc,comm,zero,not,chain` | 2 | not run | 160 |

The last row removes every rule that can prove `add y 0 = y` (`zero`, and the chain rule or builder at nested
positions), so what is left are conjectures that need that unit law itself under a bitwise operator, e.g.
`xor(y,-1) = xor(add(y,0), -1)`. A single leaf is not a sum, so `Machine::parse` rejects `y` against `y + 0`; letting
a bare leaf be a zero-carry machine would close those through the same search. Not done.

**Open.** The total-carry family is handed to the search; a search that finds it (e.g. over linear functions of the
carries, or from the leaf-bit sums) is still missing. Proof size grows with 2^(k + c) per lemma (five leaves at
n=4: seconds to tens of seconds), so c > 5 or k > 3 will need per-lemma sharing.

## 17. Bare leaves, a searched symmetric encoding, a `tree` rewrite rule, proof cost

n=4, `MINER_SAMPLE=64`; machine CPU 60-70% (other jobs running), Defender real-time protection off.

**1. Bare leaves.** `Machine` accepts an add-free term as a sum with no carries (`root`), and `prove_eq` pairs a sum
with an add-free term through `add_tree_law`, so `y = y + 0` and `x ^ -1 = (x ^ -1) + 0` are proved by the encoding
search (test `symmetric_encoding_handles_unequal_carry_counts_bare_leaves_and_five_leaves`).

**2. The total-carry encoding is now searched, not supplied.** `total_carry_encoding` is replaced by
`symmetric_encoding`: enumerate m <= 3 Boolean functions of the *number of set carries* (a table over 0..=cmax, the
same table for both sides, so unequal carry counts work), and keep the first for which both machines factor through
it (`try_encoding`, kernel-evaluated tables). The binary count is one point of that space; the search may return
another. It is used when the general table search (equal counts, c <= 3) does not apply or fails; c <= 5 and
(cmax + 1) * m <= 18.

**3. `tree` rewrite rule (`tree_step`, ablation name `tree`).** At a sum node, try 0, -1 and each variable as the
value: if `add_tree_law` finds an encoding, rewrite to it. It generalizes `zero`, `not` and `chain` (all three are
instances) and proves the unit and complement laws without any of them.

| ablated | vars | left |
|---|---|---|
| none | 3 | 0 (1842 third-variable proved; miner fingerprint pass 13 s, loaded machine) |
| `assoc,comm,zero,not,chain` | 2 | **0** (841 by the rewriter) |
| `assoc,comm,zero,not,chain` | 3 | **0** (841 + 1842 third-variable) |
| `assoc,comm,zero,not,chain,tree` | 2 | 78 (the floor without any rule that proves `add y 0 = y`) |

So with associativity, commutativity, the unit law, x + ~x and the carry-chain rule all removed, the searched
encoding alone recovers every `add` conjecture the library lemmas used to prove, with 0 kernel rejections. The last row
shows that it is the `tree` rule doing it, not another path. Cost: the unit test suite went from about 31 s to 43 s
(the rewriter now tries up to k + 2 searches at each sum node); not profiled further. Section 18 shows that
attribution was not supported: the rewriter test takes 0.8 s, the suite time is the five-carry tests.

**4. Proof cost (ignored test `tree_proof_cost_by_carries`, k = 3, left-nested vs right-nested sum of c + 1 leaves):**

| carries | build | check (n=2) | check (n=4) |
|---|---|---|---|
| 2 | 0.10-0.19 s | 0.46 s | 0.60 s |
| 3 | 0.3 s | 1.5 s | 1.6 s |
| 4 | 1.6-1.8 s | 9.6 s | 9.4 s |
| 5 | 5.2-5.8 s | 36.7 s | 34.5 s |

Cost is independent of n (the per-bit steps are cheap) and grows 4-6x per carry: it is the 2^(k + c) leaves of the
per-output case-analysis lemmas, each with a growing reflexivity term. So sharing lemmas *across bits* (already
shared by reference) would not help; what would is fewer case-split variables per lemma, for instance splitting
only on (operand bits, encoded state) instead of the raw carries, which needs a lemma that the encoding is a
function of the carries. Not done.

**Open.** The encoding search is exhaustive over tables, so it stops at five carries; the case-split cost above stops
the proof there too. Leaves are variables and constants combined by `and`/`or`/`xor`; `add` inside a bitwise leaf is
handled only by congruence (section 16), not by the encoding. Subtraction, shifts and comparison have no machine yet.

## 18. Subtraction, general bit-serial machines, proof-size trick, screening

n=4, `MINER_SAMPLE=64`. CPU 15% for the main runs (idle), 93% for the last (floor) run, whose timing is therefore
unreliable; Defender real-time protection off.

**1. Proof cost.** Writing each truth table as a closed lambda applied to its arguments (`table_app`) instead of its
Shannon expansion (which repeats each argument 2^depth times) cut the check time by about a quarter: 5 carries
34-37 s -> 26-28 s, 4 carries 9.4-9.6 s -> 6.6-7.7 s, 3 carries 1.5 s -> 1.0 s. The rest is the 2^(k + c) case
split itself; the per-leaf cost is what grows. The real fix needs a different proof shape (prove each node's
full-adder step on its own and compose with per-node state encodings, so a lemma ranges over the operand bits and
the two children's encoded states instead of all c carries); not done. The 31 s of the test suite is these
five-carry tests; the rewriter test alone takes 0.8 s, so section 17's guess about the rewriter was wrong.

**2. `sub` (the first operation without a hand-written proof).** `sub(n)` is the ripple chain with borrow
`maj(~a, b, borrow)` (the same circuit as `add` through `ripple(n, sub)`), with its own `GoodBv` preservation proof
(`good_sub`, kernel-checked) and a literal check on all 64 pairs at n=3. The miner enumerates it with `MINER_SUB=1`.
Nothing in the rewriter knows `sub`: every `sub` law is closed by the carry-encoding search.

**3. General machines.** `Machine::parse` now takes any term: nodes are add, sub (one carry each) or
and/or/xor (no carry, per-bit combination), leaves are variables and constants. So `~(x + y) = ~x - y` and
`0 - x = ~(x + -1)` (a bitwise operation over an arithmetic result) are machines too. The symmetric encoding is a
function of (number of set positive carries, number of set negative carries), where the sign of a carry is its
node's kind times the sign of the node's output in the root (the right operand of a sub is negative); for add-only
trees this is the old popcount encoding. Through a bitwise node the sign is passed on unchanged, which is only a
heuristic (the table search covers equal carry counts up to 3 regardless).
`sub_computes_is_good_and_its_laws_are_found_by_the_encoding_search` (n = 1, 2, 4): `x - x = 0`, `x - 0 = x`,
`(x + y) - y = x`, `(x - y) + y = x`, `(x - y) - z = x - (y + z)`, `x - (y - z) = (x - y) + z`,
`0 - x = ~(x + -1)`, `~(x + y) = ~x - y`, a bitwise-leaves case, and false laws rejected.

**4. `prove_eq` fallback and `tree` candidates.** `prove_eq` ends by calling the search on the pair as machines
(any pair, not only sum against sum), and `tree_step` now tries every bitwise operation of two variables or
constants as a rewrite target (so `-1 - x` becomes `x ^ -1`), not only 0, -1 and a variable.

**5. Screening.** `Term::plausibly_equals` compares two terms on the corners and 200 pseudo-random width-n tuples in
plain integers before any search, so false candidates cost microseconds.

**Results, n=4:**

| run | conjectures | unproved |
|---|---|---|
| no `sub`, 3 vars (regression) | 3871 (841 with `add`, 1842 third-variable) | 0 |
| with `sub`, 2 vars | 3122 (1934 mention `add` or `sub`) | 0 (was 66 before sections 4 and 3 above) |
| with `sub`, 3 vars | 5923 (2801 third-variable) | 0 |
| with `sub`, 3 vars, `assoc,comm,zero,not,chain` ablated | 5923 | 0 |
| with `sub`, 2 vars, those and `tree` ablated | 3122 | 0 |

The last row means the `tree` rule is no longer isolatable: the `prove_eq` fallback runs the same search on the
pair, so removing the rewrite rule changes nothing. What remains true is that none of the library lemmas
(`assoc`, `comm`, `zero`, `not`, `chain`) is needed: the searched encoding closes every conjecture, `sub` included.
The old floor of 78 is gone for the same reason, not because something else became stronger.

**Limits.** Only machines whose carries fit the table search (c <= 3 equal counts) or the symmetric search
(c <= 5) are handled, and the 2^(k + c) proof cost applies. Conjectures here are width 4 and at most two operators
deep over two or three variables; the proofs are for all widths n tested (1, 2, 4 in the unit tests), each width
built separately, not one proof for all n. The conjectures were mined by agreement on a sample of inputs, so a
false conjecture would only be caught by the kernel (none was: 0 rejections), not excluded in advance.

**Next.** (a) The per-node proof shape above. (b) Comparison (`lt_u` as a borrow-chain machine whose output is the final
borrow, not a per-bit value): the machine needs a "last bit" output mode. (c) Shifts, which break the per-position
structure (position i reads position i - 1) and need a different machine.

## 19. Hash-consing finding, new cost numbers, shifts survey

**Finding.** The slow part of the encoding lemmas was not the proof shape. The tests never entered the kernel's
`InternScope` (hash-consing, the default feature `hashcons`), so every repeated sub-expression of the symbolic truth
tables was rebuilt and re-checked. Wrapping building and checking in one scope (`InternScope::enter()` as the first
line of the tree tests and of `conjecture_miner`) gave the speedups below. The earlier `table_app` change (closed-lambda
truth table) gave only about 25%; it stays, but it was not the root cause. The scope must span both building and
checking, and the hash-cons tables live until it drops.

Measured (n=4, one proof per carry count `c`, `tree_proof_cost_by_carries`; per-iteration scope):

| c | build | check |
|---|---|---|
| 2 | 126 ms | 82 ms |
| 3 | 329 ms | 228 ms |
| 4 | 1.57 s | 1.25 s |
| 5 | 4.7 s | 3.4 s |
| 6 | 15.8 s | 8.5 s |

The lemma-size growth is still 2^(k + c), but check cost is now below build cost. At c = 6 the build dominates, mostly
the symmetric encoding search (up to 2M codes). A pruned or backtracking search would pay off before a node-by-node proof
shape would. Suite: `cargo test --release --test church_bv` 30 s -> 4.8 s to 7.4 s (23 passed, 28 ignored).

Caps raised: `cs.max > 6` and `w * m > 21` in `add_tree_law`/`symmetric_encoding` (were 5 and the old width limit).
Only the tests above exercise c = 6; the miner's conjectures need fewer carries.

**Miner inside one scope** (n=4, `MINER_SAMPLE=64`, BelowNormal; machine CPU 46.8% from other work, Defender RTP off):

| run | time | peak working set | proved / unproved |
|---|---|---|---|
| `sub`, 3 vars | 10.7 s | 1180 MB | 5923 conjectures, 2801 third-variable all proved |
| no `sub`, 3 vars | 4.4 s | 304 MB | 3871 conjectures, 841 + 1842 proved, 0 failed to check |

Memory is the cost of one long scope (tables are never freed). 1.2 GB is acceptable at n=4; a wider or deeper run should
scope per conjecture group. I have not measured the miner without a scope under the same load, so no miner speedup is claimed.

### Survey: shifts (design only, nothing built)

**Problem.** `add`, `sub`, bitwise ops are per-position machines: output bit i is a function of operand bits at i and a
carry from i-1 that the machine carries along. A shift by a constant k reads bit i-k, a fixed offset, and by a variable
amount reads a data-dependent position. The carry-machine search assumes one position at a time, so neither fits it.

**Options**

| option | idea | pros | cons |
|---|---|---|---|
| A. Constant shift as a term | `shl_k x` = bits `[0.. k-1]` false then x's low bits; `shr_k` the reverse, as a Church `Bv_n` rebuilt from x's bits | trivial to define and prove good; laws like `shl_a (shl_b x) = shl_(a+b)` are `refl` per width; no new machine | the miner must know the shift is a leaf-level rewiring, not an op with carries; composing with add (`shl_1 x = x + x`) needs the equality proved against the machine |
| B. Shift as a rewrite of the machine's inputs | treat `shl_k x` inside a machine as renaming operand bit i to i-k, i.e. a machine whose leaf at position i reads a different bit | keeps one search; lets `x + shl_1 x` etc. be handled | machine state must hold the last k bits of each shifted operand (k extra "delay" cells, like a shift register), so the state encoding search grows with k |
| C. Variable shift by a barrel shifter | log2(n) stages of constant shifts, each a mux on one bit of the amount | standard, bounded size, proofs by case analysis per stage | stages are not per-position; each stage is a leaf rewiring plus a mux, so only A-style handling applies; proof size grows with n log n |
| D. Shift by induction on the amount | a recursive definition over a unary or binary amount | one proof for all amounts | needs a Church-encoded Nat or amount type the library does not have; the kernel has no eta, so inductive proofs are costly |
| E. Do not support shifts in the search | leave them as opaque leaves | no work | the multiplication-by-constant and rotate laws then never appear in mined conjectures |

**Recommendation.** A first, B second if the miner needs `x + shl x` interplay. Reasons: A is a one-line definition
per op with `refl`-based lemmas and leaves the machine alone; B is the principled fix (a delay-line state) but multiplies
carry cells by the shift distance, which collides with the c <= 6 cap. C and D wait until a concrete conjecture needs a
variable amount.

**Related systems** (from background knowledge, not freshly fetched; verify before citing):

- SMT bit-blasting (Z3, Boolector, Bitwuzla): constant shifts become wiring; variable shifts are barrel shifters (option C).
  Multiplication and division are bit-blasted to circuits, not per-position carry machines.
- Lean 4 `BitVec` and `bv_decide`: bit-vector facts are reduced to a SAT problem by bit-blasting, then checked via a
  verified certificate. Shifts are handled by circuits, as above. That is the closest design to what this project's kernel does.
- Isabelle/HOL Word, Coq `bbv`/CompCert: bit-vectors as `Z` or lists with shift lemmas stated on the integer view
  (`shl a x = x * 2^a mod 2^n`); proofs go through arithmetic, not circuits.
- Hardware verification (e.g. ACL2 or word-level equivalence checkers): word-level rewriting with shift as multiplication
  by a power of two; bit-level only as a fallback.

The pattern across all of them: constant shifts are cheap wiring, variable shifts are circuits, and only the integer-view
systems prove shift laws arithmetically. This project's integer view exists only as `Term::interp` (a screen), not as proofs.

**Comparison (`lt_u`) status.** Not started. It needs a "last bit" output mode on `Machine` (the output is the final
borrow, not a per-bit vector), a new Church op returning `Bool0`, a goodness proof, and miner support for terms whose type
is `Bool0` rather than `Bv_n`. This unparks the section 90 circuit in the interface note.

**Next.** (a) Pruned encoding search to cut the c = 5..6 build cost. (b) `lt_u` with the last-bit output mode. (c) Option A
for shifts, once (b) is in and the miner has a typed notion of non-`Bv` outputs.

## 20. Backtracking encoding search, comparison (`lt`), constant shifts

**Encoding search (§19 next step a).** `find_state_encoding` and `symmetric_encoding` now share `label_search`: a
backtracking assignment of an m-bit label to each carry class (the whole carry vector for the table search, a
(positive, negative) count pair for the symmetric one). A raw-table row says "(operand bits, label of the class) ->
(output, label of the next class)", checked as soon as the classes involved are labelled; labels are introduced in
order, since relabelling does not change validity. This replaced enumerating all 2^(w*m) tables, so the old `w*m <= 21`
cap is gone. Measured search time at c=6, n=4: 0.42 s (c=5: 0.15 s, c=4: 0.04 s). Whole-proof build at c=6 went from
15.8 s to 11.6 s and check from 8.5 s to 7.2 s, so the search was not the main cost: **the rest of the build is the
2^(k+c) lemmas themselves.** Only the node-by-node proof shape would shrink that, and it is not built. Machine load
during these timings was 19% CPU, Defender RTP off.

**Comparison.** `lt_u(n)` is the final borrow of the `a - b` chain, returned as a one-bit vector (a `Bool0` claim would
live one universe below the `GoodBv` witness motives, so `Id(Bool0, ..)` was rejected: "inferred Type1, expected
Type2"). It is `Term::Op(5, a, b)`, root only. `Machine::last()` marks a root `lt`: the per-position output is ignored,
the machine's result is the last carry, and `label_search(.., last = true)` adds rows saying each class determines that
carry (the same function on both sides). The proof reuses the per-position chain; at the end it proves
`last carry = dec(phi(carries))` by case analysis on the carries per side and chains the two sides through the final
phi proofs, then wraps in `cong_n` to `Bv_1`. `k_var_law_to` is `k_var_law` with the claim type and final step as
parameters.

| check | result |
|---|---|
| `lt_u` computes `a < b` (7 inputs, n=4) | ok |
| `lt x x = lt y y`, `lt (and x y) (or x y) = lt (and y x) (or y x)` | proved, kernel-checked |
| false: `lt x y = lt y x`, `lt x y = lt x (y + -1)` | no proof (screen) |
| `lt` miner (ignored test): all pool pairs equal on all 256 width-4 inputs | 6780 conjectures, **3070 proved and kernel-checked, 3710 without a proof**, 0 kernel rejections, 99 s |

**Limit, and why.** The 3710 hold only on *reachable* carry states: `lt x 0 = lt y 0` (the borrow of `x - 0` never
becomes 1), and `lt (x+y) x = lt (x+y) y` (the borrow equals the add's carry, so the state (carry 1, borrow 0) never
occurs). The encoding lemmas range over all 2^(k+c) states by case analysis, so an unreachable state with a
conflicting requirement defeats every encoding. Fixing it needs an invariant per side: lemmas with a hypothesis
`I(state) = true`, a proof that `I` is preserved by a step, and an absurdity elimination for the leaves where `I` is
false. `I` could be taken as the set of reachable states, found by enumeration. That is the next step for comparison;
the same fix would also help sums whose state encodings need reachability (none have been seen so far, since the
add/sub tests all closed). Two such unreachable-state cases are pinned as `is_none()` asserts in the test.

**Shifts (option A of §19).** Built as a separate small term type `STerm` (and/or/xor, constants, constant shifts),
not as a machine: a shift reads a fixed other position, so each position's equality is a case analysis over the
(variable, source position) bits it reads (`shift_law`). `shift_bv` is the Church `x << k` / `x >> k`.
Tests: the shifts compute for n = 1, 2, 4; six laws (`shl1 (and x y) = and (shl1 x) (shl1 y)`, `shl1 (shl1 x) = shl2 x`,
`shr1 (shl1 x) = and x (shr1 (shl1 -1))`, `xor (shl1 x) (shl1 x) = 0`, `shl0 x = x`, `shl n x = 0`) check; three false
laws fail to check. Miner (ignored test): 4820 terms, 613 behaviour groups, **4207 conjectures built and kernel-checked,
0 rejected**, 2.3 s at n=4. Not covered: shifts combined with add/sub (`shl1 x = x + x`), which needs option B (a
delay-line state in the machine), and variable shift amounts.

**Next.** (a) Reachability invariants for the encoding lemmas (unlocks 3710 `lt` conjectures, and is the first thing that
the `lt`/overflow circuit of the interface note needs). (b) Node-by-node proof shape, now the only way to cut the
c = 5..6 lemma cost. (c) Shifts inside machines (option B), so `shl1 x = x + x` and multiplication by constants appear.

## 21. Reachability invariants, shared-subterm generalization, shifts inside machines

**1. Reachability invariants (§20 next step a).** Machines now carry an optional invariant: when no encoding exists over
all carry states, `add_tree_law` computes each side's reachable carry vectors (`reachable`, a search from all-false over
the raw table) and searches again with only reachable rows constrained (`try_encoding`, `label_search` take `reach`). The
lemmas then take `Id(I(carries), true)` as a hypothesis (`guarded`): the case analysis still covers every state, the
reachable ones close by `refl`, and the unreachable ones are absurd. The absurdity needs no new kernel rule:
`absurd_id` is `cong1` of `\c. mux c a b` along the hypothesis `false = true`, symmetrized. A second lemma (`pres`)
shows one step preserves `I`; the chain carries a hypothesis proof per side from `refl` at the all-false state. For a
root `lt` the final-decode lemma is guarded the same way.
Added a third search, `joint_encoding`: every carry vector of either machine is its own class (both all-false vectors
are one), so the two sides need no popcount relation; up to 5 label bits, and `label_search` now has a budget
(`LABEL_BUDGET` = 200,000 label choices, then it gives up) because a failing search is exponential.

| `lt` miner (ignored test), n=4, 6780 conjectures equal on all 256 inputs | proved and kernel-checked | without a proof |
|---|---|---|
| §20 (all-states encodings) | 3070 | 3710 |
| + reachability (per side) | 6456 | 324 |
| + joint search | **6746** | 34 |

All 34 left are width-specific, not width-generic laws: they fail the plausibility screen at some width in 1..6
(for example `lt 0 -1 = lt 0 (-1 + -1)`, true at 4 bits only), so no all-widths proof can exist. The miner now tags each
unproved conjecture by this test. 0 kernel rejections. Cost: the run grew from 99 s to 549-580 s (machine load at start
was 80% CPU from other work, so these two times are inflated; no uncontended run yet). The two laws that were `is_none()`
asserts in §20 (`lt x 0 = lt y 0`, `lt (x+y) x = lt (x+y) y`) are now proved and checked in the unit test.

**2. Node-by-node proof shape, as generalization.** A true per-node proof of a re-association needs a joint invariant
over the whole tree, so I did not build one. What does cut the lemma size is local: in `prove_eq`, a pair whose
machines have more than 3 carries first tries to turn a shared subterm (the one with the most carries) into one extra
variable, proves the pair over `k + 1` variables, and uses that proof as is (the extra variable's value is the subterm's,
by `witnessed`). That takes the subterm's carries out of the machine. Test: with `S = (x + y) + z`,
`S + (S + S) = (S + S) + S` has 8 carries per side, over the machine cap (`add_tree_law` returns `None`), and
`rewrite_law` proves it and the kernel checks it in 0.26 s; a false variant is refused. This lifts the carry limit
only for pairs with a shared block; the cost of a single machine with 5-6 carries is unchanged (§20: 11.6 s build at c=6).
Limit: a pair with no shared subterm still hits the 2^(k+c) wall.

**3. Shifts inside machines (option B of §19).** `shl1` (`Term::Op(6, a, _)`, second operand ignored) is a delay cell:
a carry whose next value is the operand's bit and whose output is the previous bit, so shifts mix with add/sub in one
machine. `shl_k` is `k` nested `shl1`s. No other code changed except the op tables and `Machine::{parse, step}`.
Unit test (n=4): `shl1 x = add x x`, `shl1 (add x y) = add (shl1 x) (shl1 y)`, the same for `sub`,
`shl1 (shl1 x) = add (add x x) (add x x)`, two commutations and `shl1` over `xor` all prove and check; `shl1 x = x` and
`shl1 x = add x y` get no proof. Miner (ignored test), pool of 1452 terms, 234 behaviour groups: 996 conjectures with at
most 4 carries per side, **922 proved and checked**, 43 carry-free (bitwise-law territory, not this search), 31 without
a proof, all width-specific (0 hold at widths 1..6); 222 conjectures with more than 4 carries were skipped, because a
first run with no cap did not finish in 40 minutes (a failing joint search at 6 carries; the budget above was added after
that run). 186 s, machine load 8% CPU, Defender RTP off. Only left shifts: a right shift reads position i+1, which an
LSB-first machine has not seen yet.

**Limits and honest gaps.** (a) The `lt` and shift miners prove each conjecture at width 4; the proofs are per width
like all of the rest. (b) Shifts with more than 4 carries per side are not mined. (c) The reachability invariant is a
per-side set; a conjecture needing a relation between the two sides' states (a joint invariant) is not covered, and
none turned up in the 6746 + 922 proved, but the 31 + 34 unproved are all width-specific so I have not seen one either.
(d) Run times for the `lt` miner are from a loaded machine.

**Next.** (a) An uncontended timing of the `lt` miner and a profile of where the 549 s go (probably the failing
`attempt(None)` before the reachable retry; trying the reachable search first when a root `lt` is present would skip it).
(b) Joint invariants (relations between the two sides' states) for laws that need them. (c) Multiplication by a
constant as a shift-and-add machine, now that shifts and adds share a machine, and a right-shift story (reverse the
stream, or MSB-first machines).

## 22. Where the `lt` miner's time goes, a three-variable check, multiplication by constants, right shifts

**1. Profile of the `lt` miner (n=4, 2 variables, 6780 conjectures).** Phases are timed inside `add_tree_law` (`PROF`) and
in the miner. Machine load at start was 13% CPU, Defender RTP off, but I ran a build and one test alongside, so treat the
absolute seconds as approximate.

| phase | time |
|---|---|
| `add_tree_law` total (search + building the proof term) | 435 s |
| of which encoding search with all states, successful | 31 s |
| of which all-states search that failed (before the reachable retry) | 0.16 s |
| of which reachable retry (reachability + second search) | 0.22 s |
| kernel check of the 6746 proofs | 219 s |
| whole miner | 654 s |

My guess in §21 (the failing all-states search before the reachable retry) was wrong: that is 0.16 s of 654. The time is
proof construction (about 400 s) and checking (219 s) over 6746 proofs, about 64 ms and 32 ms each on average. No
single conjecture is the problem, so there is nothing to skip; a cheaper proof shape per proof is the only lever (§19, §22.2).

**2. Joint invariants: evidence, not a build.** I did not build joint (cross-side) invariants. To see whether any
conjecture needs one, I ran the `lt` miner on three variables (`LTMINER_VARS=3`, `LTMINER_MAX=1500`, an evenly spaced
sample of the sorted conjectures, 1145 groups): **1493 of 1500 proved and kernel-checked, 7 without a proof, all 7
width-specific** (`lt 0 -1 = lt 0 (-1 + -1)` and similar). So there are 0 width-generic conjectures unproved in 6746 + 1500;
nothing yet needs a joint invariant. This is a sample, not exhaustive: 3-variable `lt` has more conjectures than I ran.

**3. Multiplication by constants.** `mul_const(c, t)` is the sum of `shl1^i t` over the set bits of `c`, an ordinary machine
(`shl1` cells and `add`s). Test, n=4, all prove and check: `3x = shl1 x + x` (42 ms build), `2x = x + x`, `6x = shl1 (3x)`
(0.46 s), `5x = 4x + x` (0.23 s), `7x = 8x - x` (2.8 s), `3(x + y) = 3x + 3y` (1.5 s), `3(x - y) = 3x - 3y` (1.4 s),
`(x + y) + 2(x + y) = 3x + 3y` (1.8 s); `3x = 5x` gets no proof. Also proved but left out of the unit test for time:
`3(3x) = 9x` (7.9 s build, 11.5 s with check, under load). Times were taken while the miner above ran, so they are upper
bounds. The cost growth is the same 2^(k+c) as everything else: 9x as two nested `3x` has 8 cells and carries.

**4. Right shifts (survey, nothing built).** A right shift reads position i+1, which an LSB-first stream has not produced.
Options: (a) *bitwise only* (done, §20 `STerm`): `shr` mixed with and/or/xor is rewiring, proved per position, and
`shl1 (shr1 x) = and x -2` is a bitwise law. Pros: exists, cheap. Cons: no carries across a right shift. (b) *Reverse the
vector*: express `shr` as `shl` on the reversed vector and add as a machine on the reversed bits (MSB-first); a carry then
flows the other way, which is not a ripple adder, so adds would need a different (carry-lookahead style) machine. Cons:
changes the representation of every adder proof. (c) *Look-ahead state*: let the machine guess bit i+1 as a state cell and
check the guess one position later (a non-deterministic cell, resolved by a side condition). Pros: stays LSB-first. Cons:
lemmas need a "guess is right" invariant, which is exactly the reachability-invariant machinery of §21, so it is the most
natural extension but unbuilt and its cost is unknown. (d) *Division by a power of two as an unsigned law*: prove
`shr1 x = y` by `x = shl1 y + (x & 1)`, i.e. treat `shr` as the inverse of a shift-and-add, a statement not a machine.
Related systems (background knowledge, not re-fetched): SAT/SMT bit-blasting treats shifts as wiring in both directions
because it has the whole vector at once (all positions are variables), which is option (a) generalized: the per-position
view with full bit access. The carry-machine view gives that up for carries.

**Next.** (a) A cheaper proof shape per lemma is the remaining lever on every number above (build is about 2/3 of the miner
time, check about 1/3). (b) Option (c) for right shifts, using the invariant machinery already built. (c) A wider 3-variable
`lt` run and a 3-variable shift/multiplication run, to look for a conjecture that needs a joint invariant.

## 23. Lemma cache, wider 3-variable `lt` run, right shifts reconsidered

**Lemma cache.** `add_tree_law` builds its lemmas (`F_j`, the invariant-preservation lemma `P`, the decode lemma `D`) through
`guarded`. Each is now memoized in a thread-local `LEMMAS` keyed on the side machine (`Machine::key`: leaves, nodes, root),
`k`, the side's `phi` table, the invariant table, and a tag (`F_j` adds `g[j]`; `D` adds `dec`). A lemma depends on nothing
else, so conjectures that share a side machine and encoding reuse the `Expr`. Like `CLOSED`, entries live as long as the
test thread, which also holds the `InternScope`.

| `LTMINER_VARS=3 LTMINER_MAX=1500` | before | after |
|---|---|---|
| `add_tree_law` | 281 s | 161 s |
| kernel check | 118 s | 78 s |
| total | 399 s | 239 s |
| proved / width-specific | 1493 / 7 | 1493 / 7 |

2495 lemma hits. The check time also fell (shared terms are checked once, thanks to hash-consing). Suite: 28 passed.
Machine: Defender RTP off, CPU 20-35% from other sessions, BelowNormal.

**Wider 3-variable `lt` run** (`LTMAX=6000`, 1145 groups): 5978 proved and checked, 22 without a proof, **all 22 fail at
some width in 1..6** (width-specific, so no proof can exist). No conjecture needed a joint cross-side invariant. 920 s total,
14463 lemma hits. Sample, not exhaustive: the first 6000 conjectures of the enumeration.

**Right shifts, not built.** The look-ahead cell of §22(c) cannot be a deterministic cell: its output at position `i` is
`a[i+1]`, which the machine has not read, so the cell would have to guess and be checked one step later; the g-table and
`reachable` machinery assume deterministic steps. The workable design is *retiming*: delay every other path by one
position (a `shl1`-style delay cell) so `shr1 a` reads `a[i]` at time `i` and the whole machine's output lags by one
position; the root then needs extra steps (section 26 corrects the first version of this sketch, which said an extra
zero input bit suffices: it does not). Costs: the per-position chain, the final assembly in
`k_var_law_to` and the `lt` decode all assume lag 0, so lag `L` is a change to each. Pro: reuses encodings, invariants and
the cache. Con: lag must be equal on all paths into a node (extra delay cells enlarge the carry count, the main cost
driver, 2^(k+c)). Not started; a decision for the next step.

**Next.** (a) Retiming for right shifts (design above). (b) Lemma build is still 2^(k+c); sharing one case analysis across
the `m+1` `F_j` lemmas of a side is the next cheaper shape. (c) Mine `shl` and multiplication with 3 variables (not run:
the `shl` miner caps at 4 carries per side).

## 24. Moore partition refinement replaces the three encoding searches

**Survey (before building).** Equivalence of two Mealy machines is decided by checking the start states are equivalent in
the coarsest bisimulation, found by Moore/Hopcroft partition refinement (standard; formalized for DFAs, e.g. the
Coq/Ssreflect constructive theory of regular languages, Doczkal et al. 2013). Alternative: Hopcroft-Karp pair exploration,
whose certificate is a relation on state *pairs*; its lemma would range over `k + c1 + c2` bits against `k + c` for a
quotient labelling, so the quotient (Moore on the union of both sides' states) is the better fit. The algorithm needs no
verification: the kernel checks the lemmas built from its output.

**Change.** `moore_encoding(m1, m2, k, gops, reach)` refines the carry vectors of both machines (all, or only the
reachable ones) by (final bit if `lt`, outputs, next class) until stable; the class number in binary is phi; `g` comes from
the existing `try_encoding`. It replaces `find_state_encoding`, `symmetric_encoding`, `joint_encoding`, `label_search`,
`LABEL_BUDGET` and `Machine::negative` (all deleted). `add_tree_law` still tries all states first, then reachable ones with
the invariant guard.

| run | old searches | Moore |
|---|---|---|
| 2-var `lt`, 6780 conjectures | 6746 proved, 34 width-specific | 6746 proved, 34 width-specific (420 s) |
| 3-var `lt`, 1500 | 1493 / 7 | 1493 / 7; encoding search 8.7 s to 4.6 s |
| `shl` miner | 996 conjectures (222 with >4 carries skipped): 922 proved, 31 width-specific | all 1218 (nothing skipped): 1096 proved, 79 without a proof, **0 of them hold at widths 1..6**, 815 s |

Same proved sets everywhere the old searches finished, and the 222 conjectures they could not search now complete. This is
the completeness claim in practice: every conjecture that holds at widths 1..6 and has at most 6 carries per side got a
proof. Machine for the 3-var run: RTP off, CPU 84% (other sessions), BelowNormal, so its totals are noisy.

**Remaining limits.** The 6-carry cap in `add_tree_law` is now about lemma cost (2^(k+c) case trees, plus `raw_table`
kernel evaluations), not the search; the next lever is the shared-case lemma proof (section 25, if built).

## 25. Cheaper lemma proofs: two measured negatives (code reverted)

Each lemma is a full case tree over its `k + c` bits (`lemma_n`): 2^(k+c) leaves, and `body` is rebuilt at every node.

**Survey.** Proof-producing decision procedures for Boolean identities: BDD-based rules in HOL (Shannon expansion with
node sharing, Gordon/Harrison), SAT with checked resolution/LRAT certificates (Lean's `bv_decide`). All beat a plain case
tree by sharing sub-proofs of equal residual functions. Here sharing is harder than in those systems: the kernel proves
`Id(A|p, B|p)` for each prefix `p` of fixed bits, and two prefixes with the same residual *truth table* still give
different terms (the machine side is an `and/or/xor` expression, not a canonical table), so a shared sub-lemma would
need a canonical form on both sides or an extra `trans` through a table.

**Measurement 1: potential.** A probe (env `BDDPROBE`, removed) tabulated both sides of every lemma and counted distinct
residual pairs per depth, in the given variable order: 3-var `lt`, 600 conjectures, 124,291 case-tree nodes against
22,113 distinct residual pairs (5.6x fewer). The saving exists; realizing it needs canonical forms (open).

**Measurement 2: early cut by conversion.** At each internal node, `normalize` both sides with the fixed bits substituted;
if they already agree, close the whole subtree with `refl` (kernel-checked). Same 596/4 result, kernel check 59 s to
49 s (smaller proofs), but `add_tree_law` 95 s to 249 s: open-term normalization at every node costs far more than it
saves (154 s to 298 s total). Reverted.

**Conclusion.** The conversion test is the wrong place to look for sharing. The ratio above says a table-based
canonical form is worth about 5x on build; the check side is already deduplicated by hash-consing.

## 26. Right shifts by retiming: survey and a correction (not built)

**Survey** (background knowledge, sources not re-fetched). Retiming (Leiserson-Saxe) moves registers across logic
without changing input/output behavior, up to a global latency; a negative register count on an edge is exactly a
look-ahead, and it is made legal by adding latency at the circuit's inputs and outputs. For a DAG a legal lag always
exists. Initial states can be a problem when registers move backward over logic; here they move forward (we add
delays), so zeros are a valid start.

**Applied to `shr1`.** With operand lag `la` (bit `i` available at time `i + la`), `shr1 a` is the identity wire at lag
`la + 1`. Every other operand of a node must be delayed to the same lag (delay cells, the `shl1` machinery of section 21),
and the first `la + 1` steps must not feed the operand's garbage into the carries: all streams are zero in that window if
the gate `and(shr1 a, valid)` is used, with `valid` a delay chain on `Ones` (so `shr1` costs one carry per lag step
plus one per delay).

**Why it is not a drop-in (corrects section 23).** A width-`n` term truncates every intermediate to `n` bits. Zero-extending
the inputs and running `n + L` steps is not the same: `shr1 (add x y)` at width 4 with `x = 15`, `y = 1` is
`(16 mod 16) >> 1 = 0`, but the extended sum is 16 and `>> 1` gives 8. The consumer of the operand's bit at index `n` must
be forced to 0, which is an end-of-word signal. Making that signal an input breaks the Moore equivalence (it holds only
for words that end exactly once, at the last step); making it state needs an `n`-step counter (width-specific, exponential
carries). What works is a single special final step whose equivalence is a final observation, like the `lt` decode rows:
a variant step function with `shr1` outputs forced to 0, a second lemma family for it, and `moore_encoding` taking the
variant's outputs as extra observation rows. Parts to change: `Machine::parse` (lags, delays, gates), the per-position
loop in `core` and `k_var_law_to` (n + L - 1 steps, discard the first L outputs, variant last step), `moore_encoding`, and
no `lt` at the root (the final-bit semantics interact with the lag).

**Decision.** Not built. The cost is a change in five places for `shr1` inside sums, a shape no conjecture so far needed
(bitwise-with-shift laws already have `STerm`). Revisit if a use appears.

## 27. Where the carry cap binds; sharing equal subterms in a machine

**Probe.** `mul_conjecture_miner` (new, ignored): constants up to 7, laws `(a+b)x = ax + bx`, `(a*b)x = a(bx)`,
`a(x+y) = ax + ay`, each through `add_tree_law` and the kernel; env `CARRY_CAP` (default 6) now sets the cap
(`carry_cap()`). With cap 8 and one delay cell per `shl1` node: 46 of 63 laws proved, 16 over the cap (up to 20 carries),
1 carry-free (no machine needed). Build cost per proof grows about 3x per carry: 5 carries about 1 s, 6 about 4-10 s,
7 about 30-50 s, 8 about 100-170 s. So the cap is about lemma cost (2^(k+c) case tree), not the search.

**Cause of the big counts.** `Machine::parse` made one node per occurrence, so `shl1 x`, `shl1 (shl1 x)`, ... in `15x` were
separate delay cells (1+2+3 = 6) instead of one chain with taps (3).

**Change.** `Machine::parse` makes equal subterms one node (keyed on `Term::show`). Sound: a node's stream depends only on
its operands, so two equal subterms run identical state. The same run with sharing: **61 of 63 proved**, 1 over the cap
(`7(x+y) = 7x + 7y`, 5 and 9 carries), 1 carry-free; 1229 s total because the cheaper-to-reach laws now include many 7-8
carry proofs. Effect elsewhere: the suite got faster (7.5 s from 11-13 s) and
`shared_subterms_are_generalized_so_large_sums_stay_provable` no longer needs generalization for its sum (8 carries drop
to 6), so its premise assertion was removed; generalization still serves overlap that is not a whole shared subterm.
Machine state for the timing run was not recorded (CPU load and Defender were not captured: the log held only the miner).

**Next.** The per-carry factor of 3 is the wall. Further carry reduction by sharing: Moore classes already merge states, but
the lemma still ranges over raw carries; a lemma over (inputs, class labels) of the *quotient* of each side would shrink
2^(k+c) to 2^(k+m) if the quotient step function can be proved from the machine's composition rather than by case
analysis (the compositional-proof idea, not built).

## 28. Wider mining, cap 9, and why the lemma wall needs proof-level decision diagrams

**Miners.** `shl_conjecture_miner` takes `SHLMINER_VARS` and `SHLMINER_MAX` (stride sample, as the `lt` miner) and uses
`carry_cap()`; `mul_conjecture_miner` takes `MULMINER_ONLY` (substring filter).

**3-variable `shl` sample** (`SHLMINER_VARS=3`, 800 of the conjectures, cap 6, 2265 terms, 454 groups): 696 proved and
kernel-checked, 20 carry-free, 84 without a proof, **0 of them hold at widths 1..6** (all width-specific). No conjecture
needed a joint (cross-side) invariant, and no conjecture was over the cap. 955 s, with other sessions loading the CPU
(98% at launch; RTP off).

**Cap 9.** `7(x+y) = 7x + 7y` (5 and 9 carries) proved and checked: build 440 s, total 480 s, loaded machine. The cost per
carry (about x3: 8 carries 100-170 s, 9 carries 440 s) holds.

**Sharing potential at larger carry counts** (probe as in section 25, removed again): `(2*5)x = 2(5x)` (4+4 carries): 1270
case-tree nodes against 152 distinct residual pairs; `(4+6)x`: 1270 against 166; `(5+6)x` (5+5): 2550 against 211.
The ratio grows with the carry count (8x, 8x, 12x): the case tree doubles per carry and the distinct residuals grow slowly.

**Two ways to realize it, both failed.**
1. *Memoize on the normal form of the claim* (reuse the proof of a subtree whose claim has the same `normalize`d form at
   the same depth): `(5+6)x` takes 6.6 s without it and does not finish in 300 s with it. Normal forms of open claims
   contain the unfolded Shannon tables (size 2^open bits), so normalizing at every node costs more than the case tree.
2. *Key on truth-table residuals* (what the probe counts): the subproofs are not interchangeable, because two prefixes with
   the same residual function give non-convertible terms (the machine side is a gate expression, not a canonical table),
   and the kernel would reject the reuse.

**What would work.** A decision-diagram proof (Harrison-style BDD rule): represent each signal as (BDD node, proof that
the gate expression equals the node's canonical Shannon `mux` term), and build each gate's result by a memoized apply
whose steps are instances of a few closed lemmas (`ite` distributes over a shared top variable, `mux v f f = f`,
terminal cases). It is polynomial in the BDD sizes, not 2^(k+c), and proof terms share through hash-consing. Estimated
size: closed lemmas for `ite`, a BDD with apply memo, composition for `g(u, phi(s))`; roughly 250 lines and no change to
`add_tree_law`'s interface. Not built: it is the largest remaining item and nothing measured so far needs more than
9 carries.

## 29. Proof-producing decision diagrams: built; they remove the wall, cost 1.5x below it

Measured on the shared machine (Defender RTP off, CPU 40-60% from other sessions at start and end; each miner now
prints this itself via `machine_state()`).

**Stage 0 (reduced `table_app`).** A table is now stated as its reduced ordered decision diagram (nested `mux`) instead
of the full Shannon tree. Suite 7.5 -> 4.3 s; 3-var lt (1500 conjectures) 239 -> 124 s, same 1493 proved.

**Stages 1-2 (diagrams).** `Sig` = (gate expression, diagram node, proof `Id(e, C(n))`); `Dd::apply` is memoized over
node pairs and each step instantiates a closed lemma (`same`/`skipl`/`skipr` per and/or/xor, `red`, `var`) joined by
`cong_n`/`trans_proof`. `Gates` is implemented by `GoodOps` (as before) and `DdGates`, and `term_gb`/`Machine::step`
are generic over it, so one machine definition drives both. `lemma_dd` replaces `lemma_n` for the unguarded
(`inv == None`) lemmas in `guarded`; `NOBDD=1` forces the case tree. Guarded lemmas (with invariant) still use the case
tree. The statements are identical: the diagram lemma checks against `lemma_n`'s type (test
`decision_diagram_proofs_check_and_beat_the_case_tree`; also a false equation gives `None`).

| workload | case tree | diagrams |
|---|---|---|
| 14-bit parity chain, two association orders | 2^14 leaves | build 43 ms, check 117 ms |
| 3-var lt, 1500 conjectures (<= 8 carries) | 124 s | 181 s (1.46x slower, same proofs) |
| suite | 4.5 s | 7.2 s |
| mul miner, constants <= 7 incl. sub laws, cap 14 | cap 9 reached, one law 480 s | 91 laws, 90 proved, 138 s total, slowest build 6.5 s |

The 9-carry law that took 480 s as a case tree builds in about 6 s. Below about 7 carries the case tree wins: diagram
bookkeeping (a proof per apply node, table composition) costs more than 2^(k+c) leaves when that is small. The only
unproved law is the carry-free `(1*1)x = 1(1x)` (no machine to encode).

**Decision.** Keep both paths. Default to diagrams only where the case tree would be large (nv above a threshold,
tentatively k + c >= 9); not yet implemented, so today diagrams are the default and `NOBDD=1` is the A/B switch. The
default `CARRY_CAP` of 6 is no longer a proof-cost limit; the remaining limit is the Moore partition (2^c states) and
the check of the final term.

**Open.** Guarded (invariant) lemmas still use case trees; the threshold; whether Moore refinement over 2^c carry
vectors becomes the next wall (c = 12+ is 4096 states per side).

## 30. Diagram threshold, cap 10, and why guarded lemmas stay case trees

- **Threshold.** `guarded` uses a diagram only when `nv = k + carries >= DDMIN` (default 9; `NOBDD=1` disables). 3-var lt,
  1500 conjectures: DDMIN 8, 9, 10 all 126 s (diagrams everywhere was 181 s; case trees only 124 s), same 1493 proved.
  No lemma in that run reaches 8 bits, so the threshold only protects small cases.
- **Cap.** `CARRY_CAP` default 6 -> 10 for unguarded lemmas. Measured effect: 2-var lt (6780 conj.: 6746 proved, 34
  unproved, 236 s) and 2-var shl (1096 proved, 79 unproved, 124 s) are identical at cap 6 and 10, nothing there exceeds
  6 carries. Mul laws (constants <= 7, 91 laws) go 61/63 -> 90/91 at the default, 129 s. Guarded (invariant) lemmas are
  case trees, so they keep a cap of 6 carries.
- **Guarded lemmas on diagrams: not built.** `GUARDTRACE=1` prints every guarded lemma built: zero in the lt, shl and mul
  miners and in the whole suite. Every proved law so far has an unconditional encoding, so the reachable-states path is
  not exercised; building a diagram version (conditional equality via `a = a&I = b&I = b`) has no measured use.

## 31. Mul laws to constant 12: no wall up to 11 carries

`MULMINER_MAX=12 CARRY_CAP=14` (BelowNormal, Defender RTP off, CPU 9-19%): 246 laws, 245 proved and checked, 0 over the cap,
722 s. The one miss is the carry-free `(1*1)x = 1(1x)`. Largest machines 9 to 11 carries per side; slowest single build
15.5 s (`11(x-y) = 11x - 11y`, carries [6, 11]), the next 12.8 s. Per-law build time grows about 1.5x per added carry, not
3x as with case trees, and the Moore partition has not been the limit yet (2^11 = 2048 states). Reproduce with the command
above; log was `%TEMP%\mul6.out` (not kept in the repo).

## 32. Ablation audit and the mathers survey: the midpoint is canonical, so lemma-finding is not the hard part here

**Survey of `../mathers`** (Metamath backward search over set.mm, bag-of-symbols policy that only orders candidates, no
value net; report by a subagent over `selfplay-burn/RESEARCH_NOTES.md`, not yet spot-checked by me). Findings that matter
here: a perfect ordering is worth only about +5-8 hits per seed (about 4%); self-play data adds at most about 2 theorems
after the forward-reference fix (earlier eval counts were inflated by unverified proofs, about a quarter); the real
bottleneck is variables that occur only in a hypothesis (the ax-mp gap), with metavariable search the open next step;
methodology worth copying: kernel-verified proofs only, a deterministic pure-ordering ranker, multi-seed McNemar,
an audit that classifies why a step is unreachable, an oracle ceiling measured before any learner. The unifier is
string-span matching with no conversion, and the policy is a label classifier, so neither transfers.

**Mapping.** The ax-mp gap corresponds to the `trans` midpoint. In the machine proofs the midpoint is the pair
(phi encodings, tables `g`), and `moore_encoding` computes it as the coarsest bisimulation: unique, no branching, no
oracle needed. `ablation_audit` (ignored test; `MULMINER_MAX`) measures what it must produce, over the 91 mul laws
(constants <= 7, all proved):

| phi bits | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|
| laws | 5 | 14 | 36 | 25 | 7 | 4 |

- Carry vectors compress heavily: 512 states (9 carries) to 4 phi bits (<= 16 classes) for `7(x+y) = 7x + 7y`; `g`
  tables of 320 bits.
- Moore is 2.6 s of 70.6 s total proof time (4%); the diagram lemmas dominate.
- With the midpoint given, every ablated lemma `Id(F_j, G_j(bits, phi))` is closed by the diagram prover, so the
  lemma-proving ceiling is 100% for these laws; an ablation changes no result. The AI-search question shifts to
  library-level proofs (a law proved by citing other proved laws), which nothing here exercises: all proofs are direct.
- Machine state: Defender RTP off, CPU 21% at the end.

**Consequence for the long-term goal.** For the machine-expressible families (add, sub, shl, lt, constant multiples)
nothing is left to search; lemma discovery would matter for laws outside them (right shifts, nonlinear terms, anything
with no finite-state machine) or for compositional proofs reusing earlier laws. Next measurable step: a rewrite-based
prover over the proved-law library with ablation, using mathers' harness discipline (verified-only, deterministic
ranker, oracle ceiling first). Not built.

## 33. Survey spot-check, right-shift demand probe, library-level prover options

**Spot-check of section 32's survey** against `mathers/selfplay-burn/RESEARCH_NOTES.md` (fresh reads): confirmed the
oracle table (lines 1537-1553: oracle order +5-8 per seed over x50s2, about 4%; pruning to set.mm's labels loses
badly), the budget sweep (2k/8k/32k/128k: 115/128, 138/143, 152/154, 161/161 dev unranked/ranked), the forward-reference
inflation (about a quarter, line 476-478), and "self-play adds at most ~2%" (lines 1586-1593). One refinement: the
policy itself clearly helps over unranked search (p <= 0.003, 2-4% of the union per seed); only the *self-play data*
is within noise. The notes' pre-fix oracle table (line 1377, +12) is superseded by the redone one.

**Right-shift demand probe** (`tools/shr_probe.py`, python, not Rust): all terms over x, y with add, sub, and, or, xor,
shl1, shr1 up to 6 nodes (6746 terms), grouped by value at widths 3-6 (exhaustive to 4, sampled at 5-6). 1316 classes have
more than one term (candidate laws); 879 involve `shr1`; **190 involve `shr1` applied to an operand containing add/sub**,
the case the machine model cannot take (e.g. `shr1 (shl1 x) = shr1 (add x x)`, `shl1 (shr1 x) = add (shr1 x) (shr1 x)`);
45 classes equate a `shr1` term with a shr-free one. So right shifts are about 14% of the equations at this size
(some are bitwise-trivial duplicates, e.g. `or x x`; no dedup was done, so read it as an upper bound). That is real
demand, and the section 26 design (five places to change, a variant last step, extra observation rows) stays the way in.
Not built.

**Library-level prover (the open AI-search question): options, before choosing.**
1. *Rewriting with proved laws* (Lean `rw`/`simp`, HOL rewriters; equality saturation like `egg`). Pros: sound by
   construction, kernel proofs are `cong`/`trans` chains we already emit; the proved-law library is the rule set;
   ablation is "remove a rule". Cons: needs matching up to our Church encodings (conversion), orientation and
   termination choices, and an e-graph proof-producing layer for the saturation variant.
2. *Conjecture-then-decide* (what the miners do: propose, check by evaluation, close with the machine/diagram prover).
   Pros: already built, 100% on machine-expressible laws. Cons: no reuse of earlier laws and no notion of lemma, so it
   cannot be ablated in the sense of the goal.
3. *Learned ordering over rewrite choices* (mathers' ranker). Pros: harness exists. Cons: mathers measured ordering as
   worth about 4%; the gap there was invention of terms, which here is decided by Moore. Premature.
4. *Bit-blast to SAT/BDD with proof logging* (cvc5/LFSC-style). Pros: complete for fixed width. Cons: width-specific,
   which is exactly what the n-uniform proofs avoid.
Recommendation: option 1 on a small rule set, measured against option 2 as the oracle: pick laws whose direct proof is
big (11-carry multiples) and see whether rewriting from smaller proved laws gives a smaller proof; ablate rules; report
the oracle ceiling first. Cost estimate: matching on `Term` (not Church expressions) with a bridge to the existing
`cong_n`/`trans` emitters; a few hundred lines. Not started; awaiting a go.

## 34. Rewriting from a proved law beats the machine proof; ablating the law is measurable

The repo already had a rewriter (`rewrite`, `prove_eq`, `rewrite_law`: assoc, comm, identity, `a + ~a`, carry-chain and
tree steps, with env `ABLATE=zero,comm,assoc,not,collapse,chain,tree`). This step adds one library law to it: **`shldist`,
`shl1 (p + q) = shl1 p + shl1 q`**, proved once per width by `add_tree_law` and instantiated at the values and good
witnesses of `p`, `q` (new `shl1_op`, `good_shl1` via `good_vec`, `witnessed` case for op 6; `abstract_atoms` treats
`shl1` as an atom like `add`). `rewrite` pushes shifts to the leaves, the existing assoc/comm normalizes the sums, and
`prove_eq` closes with `refl`.

Test `rewrite_from_the_shift_law_versus_the_machine` (ignored; `MULMINER_MAX`, `ABLATE=shldist`): `c(x+y) = cx + cy` at
width 4, build / check, same kernel check on both sides (Defender RTP off, CPU 32-48%):

| c | with the law | `ABLATE=shldist` (machine proof) |
|---|---|---|
| 3 | 140 / 131 ms | 556 / 452 ms |
| 5 | 21 / 54 ms | 1.35 / 1.31 s |
| 7 | 71 / 72 ms | 4.7 / 5.2 s |
| 9 | 26 / 34 ms | 3.5 / 3.4 s |
| 11 | 78 / 33 ms | no proof (11 carries, over cap 10) |

So the lemma is worth 15-70x here, and removing it is the ablation that matters for the goal: **the value of a lemma is the
proof cost it saves**, measured by the same call with the rule switched off. With the law, 11 carries needs no machine at
all. The machine route is the fallback that proves the law itself (2 variables, 3 carries).

**What this does not show.** The rule set is one hand-chosen law plus the existing hard-coded steps; the rewrite
engine is still a fixed strategy (bottom-up, assoc-right, sorted), not a search over which law to apply. The
discovery question (finding `shldist` without being told) is where a search would enter: candidates are mined laws
(sections 22-28) that, as rewrite rules, shrink a target's machine. Next measurable step: take the mined library
(shl, mul, lt laws) as rules, add rule matching on `Term` patterns, and ask for each large target which rules reduce
its carries.

## 35. A rule library for the rewriter; ablating rule families over all 246 mul laws

Section 34's hard-coded `shldist` is now data: `Rule { name, lhs, rhs }` (patterns over `V(0)..`), first-order
`match_pat`/`subst_pat`, and `rule_step` which proves each rule once per width with `add_tree_law` on the patterns and
instantiates it at the matched subterms' values and good witnesses. Four rules: `shldist` (`shl1 (p+q)`), `shldistsub`
(`shl1 (p-q)`), `double` (`p + p = shl1 p`), `doublechain` (`p + (p + r) = shl1 p + r`); `ABLATE` takes the rule names.
Test `rewrite_rules_over_the_mul_laws` (ignored; `MULMINER_MAX`, `CARRY_CAP`) runs every mul law through `rewrite_law`
(width 4, kernel-checked) and counts whole-term machine proofs still needed (`MACHINE_FALLBACKS`).

Constants <= 12, cap 14, three jobs at once at BelowNormal (CPU 43-45% by the end, so times are contended; Defender RTP off):

| rules | proved | no whole-term machine proof | wall |
|---|---|---|---|
| all four | 246 / 246 | 183 | 377 s |
| `shldist`, `shldistsub` ablated | 246 / 246 | 106 | 728 s |
| `double`, `doublechain` ablated | 246 / 246 | 104 | 1120 s |
| (machine only, section 31) | 245 / 246 | 0 | 722 s |

Rule instances used (all rules): `shldist` 205, `doublechain` 100, `double` 55, `shldistsub` 31. The extra proof over the
machine route is the carry-free `(1*1)x = 1(1x)`.

Reading: every law is provable without any rule (the fallback machine proof of the normalized terms is itself cheaper
than the original), so ablation here changes cost, not provability: removing either family roughly doubles to triples the
wall time and cuts the machine-free share from 183 to about 105. The two families are complementary (the shift rules
reduce more instances, `double` rules matter for products `a(bx)`). 63 laws still need a machine proof of the normalized
pair (<= 16 s each, mostly differences and 3+ factor products): the next rules to mine are the ones that remove them.

**Right shifts (item 3 of the list).** Not built. The rewrite route changes the estimate: laws mixing `shr1` with sums
need either the section 26 machine change or per-position lemmas; the 190 classes from section 33 were not yet
classified into "STerm-provable" versus "needs adds". That classification is the next measurement before any build.

## 36. Mined rules, the low-cap ablation, and the right-shift classification

**Low-cap ablation (`CARRY_CAP=6`, constants <= 12, four jobs at once, Defender RTP off).** Provability now changes:

| rules | proved of 246 | machine-free |
|---|---|---|
| all four | 230 | 181 |
| `double`, `doublechain` ablated | 205 | 102 |
| `shldist`, `shldistsub` ablated | 187 | 104 |
| none | 178 | 57 |

So the rules are worth 52 laws at cap 6 (and 53 of the proved ones lie beyond the cap): a lemma's value is both cost
(section 35) and reach.

**Rule miner** (`rule_miner`, ignored; env `MULMINER_MAX`, `RULEMINER_TRIALS`, `RULEMINER_SIZE`). Goal-directed: the
targets are the *stragglers*, the mul laws (constants <= 7) that still needed a whole-term machine proof under the
built-in rules (19 of 91). For each arithmetic subterm of a straggler's normalized terms it enumerates abstractions
(cut subterms into at most two variables), looks up smaller terms with the same width-4 function in a pool of all terms
of up to 5 nodes (4020 terms, 276 distinct functions), keeps the smallest right side per left side (31 candidates),
requires `add_tree_law` to prove it, then tries it as an extra rule on every straggler (step budget 200 per trial; a
candidate that undoes a built-in rule cannot loop) and scores by machine proofs removed. Greedy cover chooses
`sub(add(x,y),y) -> x` (+4), `sub(add(x,y),x) -> y` (+2), `sub(add(shl1 x, y), x) -> add(x,y)` (+2) and six single-use
rules: 14 of 19 stragglers covered; uncovered: `a(x-y) = ax - ay` for a = 3, 5, 6, 7 and `(7-5)x = 7x - 5x`.
Two earlier negatives are worth keeping: a fixed pool (two-variable shl pool) produced 24272 candidates and none
helped, because the needed laws were depth-2 shapes it never contained; and rules must also be tried at `sub` nodes
(the miner found nothing until `rule_step` was added there).

**Out of sample.** Promoting the two general rules (`cancelr`, `cancell`) to built-ins and rerunning all 246 laws
(constants <= 12, cap 14, one job, CPU not measured at the end): 246 / 246, machine-free 183 -> 196, 377 -> 256 s (the
earlier run shared the CPU with two other jobs, so the time gain is partly contention). 16 instances in total.
In-sample caveat: the rules were mined on constants <= 7; the 246-law run is the held-out check.

**Right-shift classification** (`tools/shr_probe.py`, sizes <= 6). Of the 190 classes with `shr1` over arithmetic, 50
have a member with no add/sub at all (so `STerm`'s per-position prover reaches that side), and in 33 of those the only
arithmetic is `add p p`, which the `double` rule already turns into `shl1 p`. The other 140 contain `shr1` over real sums
or differences (and many are `or x x`-style duplicates, not deduplicated, so this overstates), which needs the section 26
machinery. So roughly 17% of the hard classes (33/190) are within reach of the existing rule engine plus a shr congruence
step; building that step first (shr as a unary congruence node plus `STerm` leaves) is cheaper than section 26. Not built.

## Continued in part 2

Sections 37 onward are in `2026-10-02-search-execution-blend-design-part2.md` (this file was split at 136 KB so a new session can read
section 0 and the survey without the full log). Section 0 above is kept current and points to the sections in either file.
