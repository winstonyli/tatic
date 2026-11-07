## The JIT and the target machine

### Compiled evaluation, the wasm JIT and a formal target machine (2026-10-13 to 10-17)

**Compiled evaluation for conversion, and the wasm JIT (survey, no code, 2026-10-13).** The profile now favors
evaluating faster rather than less, the case Rocq's `vm_compute` and `native_compute` serve. The repo's JIT
(`crates/tatic/src/jit.rs`, `compile.rs`, `lower_wat.rs`) is not that tool:
- It compiles `term.rs` programs typed `Int -> ... -> Int` to wasm, not kernel `Expr` (with `J`, `WRec`, `SigRec`).
  Nothing in `tatic-kernel` or `crates/church-bv` calls it; the kernel checks the JIT's proofs, not the reverse.
- It is not end-to-end sound by its own account: its kernel theorem is stated over `proof.rs`'s `denote`, a model of
  the compiler, not over the WAT that runs (`crates/tatic/src/jit.rs` header). Using it, or anything like it, for conversion would put
  the compiler, wasmtime and the postulated `Int` in the trusted base.
- The 2026-09-30 options table (bitvector spec §35, row 7) already rated native/VM reflection "trusted base grows; does
  not help the symbolic lemma", verdict "different problem".
- The ceiling is modest (estimate, not measured): `conv_rc` is 39% of busy samples and the leaf evaluation 72% of its
  reduction work, so even free evaluation would save about 28% of the run.
- "Self-improving" in these docs is the rule-mining loop (proved laws compiled into rewrite rules), not a kernel
  compiling its own hot paths; no design for the latter exists.

The cheapest test of the idea is an untrusted evaluator timed on the same conversions: if a closure-based one cannot
beat the kernel there, a compiled one would have to win on constant factors alone.

**`kernel_lazy` on today's conversions: 64-100x slower (probe, reverted, no patch kept, 2026-10-13; the module itself was deleted in 306a968).** At a357781,
`proof_cost_split` cmp3d own's work (the 300 laws, building and checking, then the rule proofs) with each `check_rc`
query whose sides are not `==` timed in place (the kernel's `def_eq` as it runs, with that check's memos), logged, and
replayed through `def_eq_lazy_shared` (closed-node memo, reset per query). CPU about 28% at the start, Defender RTP off.
The run was stopped by a 3 GB memory guard during the 27th rule proof (`kernel_lazy` reached 3.3 GB; an unguarded run
reached 5.9 GB after 10 CPU-minutes):

| | Batches | Queries | Kernel in place | `kernel_lazy` | Ratio (per batch, kernel over 5 ms) |
|---|---|---|---|---|---|
| laws (build and check) | 300 | 36.2 k | 0.22 s | 22.2 s | 100x (19-69x) |
| rule proofs (26 of them) | 26 | 45.1 k | 1.13 s | 72.8 s | 64x (23-146x) |

Agreement was counted but not printed before the guard stopped the run, so it is not known here. Replaying the kernel after the check instead, while
the outer scope's tables still held the reductions, took 3 µs a query, which is why the kernel is timed in place. On
2026-09-30, before hash-consing, the same evaluator was level with the kernel at n = 32; the tables since then put the
kernel about two orders of magnitude ahead on this workload. So a faster untrusted evaluator is not in reach by changing
the evaluation strategy, and a compiled one would need a constant-factor gain above 60x over closure evaluation just to
draw level, before its trusted-base cost. Not pursued; the JIT thread stays separate from conversion.

**A general symbolic mechanism in place of the case trees? (survey, no code, 2026-10-13).** Ranked by end-state design,
not effort. `lemma_n` is already one general mechanism: any Boolean equality over `k` good bits, proved by splitting
every bit with `refl` leaves. Its callers are the machine proofs' `F`, `P` and `D` lemmas (`guarded`, `machine.rs`),
`bitwise_law_k` (`rewrite.rs`), `pos_law`'s per-bit lemmas (`machine.rs`), and a few tests. No caller special-cases a
gate. Candidates:

| Candidate | End state | Verdict |
|---|---|---|
| Per-gate symbolic lemmas (`and`, `xor`, mux laws), composed by congruence | One lemma per gate, plus a canonical form to meet the table side `G_j`, which is a mux tree, not a gate circuit | More special cases than now; rejected |
| Proof-producing canonical forms (decision diagrams with a proof per node) | One mechanism, as general as `lemma_n` | Built and measured: lost at nv = 9 and 11, deleted ("Decision diagrams deleted") |
| Reflection: a Boolean-expression syntax (a `W` type), its denotation, a checker, and one kernel-checked soundness theorem; each lemma is the theorem applied to syntax with `refl(true)` | One mechanism, as general as `lemma_n`, with four new concepts in place of a 40-line builder (`lemma_n`, `lemma_n_ty`); trusted base unchanged | Not cleaner. Faster only if the kernel's evaluation of the checker beats the leaves. A truth-table checker repeats the same 2^k evaluations with interpretation on top. A diagram checker means the kernel runs diagram operations on Church-encoded data, at k <= 9 (mostly 7), where the proof-producing diagrams already lost (estimate, not measured) |
| One tree per side for all its `F_j` | Same mechanism, fewer trees | Parked above (at most about 7%) |

So no candidate is a cleaner end state than `lemma_n`: the case tree is the general mechanism, and the alternatives are
either special cases or the same generality with more parts. The thread stays closed. One by-product of the
`kernel_lazy` probe: the 26 rule proofs carry 1.13 of the 1.35 s of conversion `proof_cost_split` timed (84%). The
loop checks each rule proof once per library (`shared_lemma`), so `proof_cost_split` weights them more than serving
does.

**Other ways to join the JIT and the loop (survey, no code, 2026-10-13).** The two already state one idea: `jit.rs`
opens with "if a high-level transformation is found to be equivalent to a low-level sequence of operations on the
target machine, use that for future invocations", and the loop compiles proved laws into rewrite rules. Today they
share nothing:

| | JIT (`crates/tatic/src/`) | Loop (`crates/church-bv`) |
|---|---|---|
| Terms | `term.rs`: `Int` is i64, wrapping (`eval.rs:137-150`); `Add Sub Mul Div Mod Lt Le Eq` (`term.rs:15-23`), `Lt` signed; no bitwise ops or shifts | `rewrite.rs` `Term`: width-n words; `add sub xor and or shl1 shr1 lt`, `lt` unsigned (`rewrite.rs:58`) |
| What is proved | a term equals its compiled form, over `proof.rs`'s `denote` (a model of the compiler) with `Int` postulated | a law, by the kernel, at one width (`prove_rule(n, ..)`); width-generic proofs are not built |
| Reuse unit | a term's content hash | a rewrite rule (and closed lemmas as parameters, `shared_lemma`) |
| Rewriting | `specialise.rs` only inlines known closures; `spec_check` accepts only beta-v steps | `rule_step` over the mined library |

Options, ranked by end-state design (fewer concepts, fewer special cases):

| | Option | End state | Risks and open questions |
|---|---|---|---|
| A | One term language and one rule library for both: `term.rs` gains the loop's word operators (i64 as width 64), mined laws become rewrite steps the specialiser may take, and `spec_check` accepts a step that instantiates a kernel-checked law; the JIT's compiled terms feed the miner as conjectures, scored by compiled cost (as Souper ranks by instruction count) | Two term languages, two rewriters and two notions of "proved equivalent" become one each; the cycle closes on real workloads | Laws are proved at one width (4 in `proof_cost_split`), and the width 1-6 screen does not imply width 64: needs width-generic proofs or proofs at 64. Signed `Lt` against unsigned `lt`. `proof.rs`'s `Int` is a postulate with no bits, so it needs a bridge to the bitvector encoding. Compilation itself stays trusted (`lower_wat`, wasmtime) |
| B | Compile the mined library into a matcher (for example a discrimination tree), rebuilt when the library changes | Same concepts, faster `rule_step`; untrusted, the kernel still checks every proof | Rewriting is 4.5-6% of the sweep's loops after the rule-list fix ("Where the time goes in the sweep's loops"); wasm adds nothing over a Rust matcher |
| C | The JIT as the miner's evaluator (screens, signatures, scoring) | A second evaluator for the same `Term` | The one large evaluation cost found, the pool's behaviour signatures (`SigMemo`, 56% of serving), was a rebuild per process, fixed by building each family's pool once ("Law files from the driver"); no later profile puts the screens high. Rejected |
| D | Compiled evaluation for kernel conversion | | Closed above (`kernel_lazy` 64-100x behind; trusted base grows) |

A is the only option that removes concepts; B and C each add a second implementation of something that exists. A's
cheapest falsifier is additive and leaves no rework: on the JIT's own corpus (`src/test_corpus.rs` then; `samples::corpus()` since c002e6f), count the terms
that the mined `add`/`sub` rules would rewrite (ring identities, which hold at every width) and the change in compiled
instruction count. If the mined rules never fire on the JIT's programs, A's cycle has nothing to run on.

*Result (2026-10-17, probe reverted; `docs/runs/2026-10-12/patches/option_a_probe.patch`): nearly nothing to run on.*
The 24 distinct add/sub-only rules in the 11 mined and hand rule files (of 203 rule lines; the rest use `lt`, `xor` or
shifts, which `term.rs` lacks) were matched against every node of `crates/tatic/tests/rule_match_census.rs`'s 19 builders (the
benchmark terms, so `test_corpus` less its two `(150)` loop variants and three IR fixtures, plus
`redundant_arithmetic_recursion`): 286 nodes, 32 of them add or sub, 4 an add or sub over another. Two rules fire, both
on one node, `add(sub(v2, v1), v0)` in `over_application_if_between_closures`, and both only reorder it: 0 instructions
saved (no operator removed, no constant left foldable). The other three nested nodes are `add(add(..), ..)`, which no
mined rule rewrites, and the planted `x + 0`. The JIT's programs are loops and closures over `n - 1` and `a + b`; the
miner's laws are about deeper word arithmetic. So A's cycle needs workloads with arithmetic depth (or the JIT's
specialiser to produce it, by inlining) before its rules can pay; unifying the term languages stands on concept count
alone, not on measured gain.

*With the class table in place of the rules (2026-10-23, probe reverted; `docs/runs/2026-10-23/patches/jit_table_probe.patch`):
the same answer.* Each maximal add/sub tree of the same 19 builders became a table term (literals 0 and -1 as the
constants; every other subterm, other literals included, an atom by identity) and was replaced by `Classes::canonical`.
There are 28 such trees, none with more than three atoms; the table changes 4 and saves 1 operator in all: the planted
`add(add(x, 0), y)` to `add(x, y)`, which no mined rule rewrote. The other three only reassociate (`add(sub(x, y), z)` to
`sub(x, sub(y, z))`, `add(add(x, y), z)` twice). A normal form cannot help where the trees are one operator over leaves;
option A still needs workloads with arithmetic depth.

*Hacker's Delight routines, a workload with arithmetic depth (2026-10-31, probe reverted; `docs/runs/2026-10-31/patches/hd_probe.patch`):
the table and the base rules rewrite most of them; the 156 mined rules add nothing.* 25 routines written the long way in the
loop's term language (constants 0 and -1 only, so `1` is `sub(0, -1)`; `shl1` and `shr1` take a second operand; `lt` is
assumed to give 0 or 1): trailing-bit tricks, averages, min/max by `lt` mask, the add/sub/and/or/xor interconversions, bit
select, majority. 80 operators in all. `Classes::canonical` changes 17 and leaves 54 (26 saved, 33%); a `rewrite` at width 4
under the base rules plus the 156 mined rules of `v06-icount/out_sm/cold_streams_streams_3_none` changes 19 and also leaves
54, and with no mined rules the total is the same 54 (the extra two changed terms only reorder operands of the `lt` mask).
The table's savings are the textbook identities (`add` via xor/and to `add(x, y)`, 4 to 1; `sub` via and/not, 5 to 1; the
de Morgan `or`, 4 to 1; `majority`, 5 to 4 via `xor(x, and(xor(x, y), xor(x, z)))`), and it reaches `x` from a swap-xor
leftover. Misses: the already-short forms (isolate lowest 1, clear lowest 1, averages, bit select) stay as written, as they
should, and `lt`-mask min/max do not shrink, so no routine shows a gain from a mined rule over the table. Reading: this
workload has depth, and the table (the fixed base rules too) is what finds it; it does not separate a learned proposer
from the fixed machinery, so it is not the next milestone's test by itself. The routines are my own transcriptions in the
long form, not a fixed external corpus; the 33% is an upper-bound illustration, not a rate.
The routines now live as the corpus `docs/corpora/hd-own/` (`corpus_report` reproduces the 80, 54 and 17; the probe patch is
superseded).

*Souper's `test/Infer` agrees (2026-11-01; `docs/corpora/souper/`, commit `963d4df`).* Of its 39 files 14 fit the term language
(Hacker's Delight P1 to P7, P10 to P12, P14, P15, P17 and `const1`; the rest need `mul`, `select`, width-specific shifts or
other constants, listed per file in `SOURCE.md`): 52 operators, the table changes 10 terms and leaves 42, and the base rewriter
also leaves 42. As in `hd-own`, the table does the rewriting and nothing is left for a mined rule. Only P10 to P12, P17 and
`const1` are new shapes, since the rest repeat `hd-own` routines; the corpus is mostly the same book, so it is not independent
confirmation of the 33%. P10 and P12 (from `ule`) first panicked the measurement: `abstract_atoms` (`rewrite.rs`) listed the
non-bitwise operators without `lt`, so an `lt` word under a bitwise operator reached the bit-level evaluator; fixed, with a test.

*Does the specialiser produce arithmetic depth? No (2026-11-01, probe reverted; `docs/runs/2026-11-01/patches/specialise_depth_probe.patch`).*
The 23 terms of `samples::corpus()` before and after `specialise` (12 of them take at least one inlining step): the maximal
add/sub trees (an `Add` or `Sub` not directly under another), by operator count. Before: 33 trees, 4 with two operators, none
with three, largest 2. After: 34 trees, the same 4, none with three, largest 2 (one extra single-operator tree, from
`twice_inc_5`). Inlining a known closure puts a body into a call site, but the bodies are single operators over loop-carried
variables, so nothing composes into a longer chain. This closes the parked trigger "or the specialiser producing it by
inlining" for this corpus: it does not, so a workload with depth has to be written, not derived. Limits: 23 small terms, the
specialiser inlines only known closures, and a count of trees does not measure what a larger program would give.

**Laws uniform in the width: two of them check on the unchanged kernel, and one reaches `Bv_n` (spike, 2026-11-01;
`crates/church-bv/src/uniform/width.rs`).** The route is option 3 of `docs/superpowers/specs/2026-10-02-search-execution-blend-design-part2.md`
§53: bits as streams, a bit-serial adder whose carry is a fold, and induction on the position. The kernel has no cumulativity,
so one Church `Nat` cannot index the inputs and also count the fold (the state would mention its own type); the spike uses
two, `Nat_k` for the streams' index and `Nat_(k+1)` for the count, with the state `Sigma(Nat_k, Bool0)` (position numeral,
carry). Checked, uniformly in the position N and with per-bit `GoodBool` hypotheses on the stream bits as in
`crates/tatic-kernel/tests/church_lemmas.rs`: `add x 0 = x` and `add x y = add y x`, plus the prefix form for every n (about 1 ms each at k = 0).
Five false laws are rejected (one control, `add x y = x xor y`, is only ill-typed, so weak). `add x 0 = x` is one induction
whose statement is the state equality `st M = (embed M, false)`; two statements (`fst = embed`, `snd = false`) would put an
`Id` on `Bool0` in the induction motive's sort, which is only `Sort(k+1)`, and it checks at every level k = 0 to 3.

*The bridge to the fixed-width tuple works (`bridge_add_zero`, n = 1 to 32).* `Pi x:Bv_n. GoodBv x -> Id(Bv_n, add x 0, x)`, the
statement of `encoding::add_zero_proof` itself, is proved from the uniform theorem. Inside the `GoodBv` step the bits `a_i` and
witnesses `ga_i` are variables; the stream reads them off with a lookup `i Cw proj0 rot a.. ga..`, where `proj0` picks `a_0` and
`rot` shifts the tuple by one and pads with false. The uniform theorem asks for `GoodBool (x i)` at every position, a `Sort2`
claim, so the lookup must return `W = Sigma(b:Bool0, GoodBool b)`, and a `Nat_k` eliminates only into `Sort k`: the index is a
`Nat2` and the count a `Nat3` (k = 2). Each output bit is the theorem at the numeral i (its `Good` witness a closed term), and the
tuple equality is a chain of rewrites of those bits. The adder's carry circuit is `encoding::ripple_carry`'s, so the stream
adder's bit i is convertible to `encoding::add`'s and no circuit-equivalence proof is needed. Wrong statements (`add x 1 = x`, and
`add x 2^(n-1) = x`) are rejected at n = 1 to 3. Cost, one run, shared machine: the bridge checks in 0.8 ms at n = 4, 1.5 ms at 8,
5.1 at 16 and 21.9 at 32, while `add_zero_proof` checks in 0.2, 0.4, 0.9 and 2.7 ms, so the bridge is about 8 times slower to
check here, and building its term costs 14 ms at n = 4, 82 ms at 8, 631 ms at 16 and 6.1 s at 32 (the numerals and `Good`
witnesses are O(i) each: quadratic). It is not a speed win. What it shows is that a law proved once for every width is the same
statement as the fixed-width law, so a uniform proof can serve every `Bv_n`; each n still needs its own bridge instance, not one
for all n. (The 70 ms at n = 8, 3.4 s at 32 and 32.6 s at 64 quoted for per-width proofs earlier come from the bit-vector doc, §17-21,
a different construction; `add_zero_proof` is far cheaper, so those numbers are no baseline for this.) So "the kernel lacks an
induction principle" in the parked goal-D entry is too strong for `add`.

*The same route carries the bitwise and `lt` laws (`crates/church-bv/src/uniform/bitwise.rs`, 2026-11-01).* Four bitwise laws
(`xor x x = 0`, `and` commutes, absorption, De Morgan; the last two nest operators) and `lt x x = 0`, `lt x 0 = 0` are proved
uniformly in the position and bridged to the statements of `encoding::bitwise` and `encoding::lt_u`, accepted at n = 4, 8, 16,
24 and 32 (default tests check n = 1 to 3), and wrong statements are rejected (well-typed and false, by the reviewer's mutation
checks). The bitwise laws are uniform only in the trivial sense (a per-bit lemma over positions, no induction); `lt` is the
second real induction (the borrow chain, circuit of `ripple_carry(sub=true)`). The encoding has no per-width proof of these
laws, so the baseline is a per-bit case split written in the same file: it checks at 2.0 to 3.2 ms at n = 32 against 3.6 to
4.4 ms for the uniform route, and builds in 8 to 25 ms against 39 to 77 ms (reviewer's run, shared machine). Again no speed win.

*`mul` is only partly reachable (`crates/church-bv/src/uniform/mul.rs`, 2026-11-01; over Church numerals, see "The level wall is Church's" below).* A single fold over the multiplier's positions
is ill-typed: the stream adder raises the index level (`Bits(k) -> Bits(k+1)`) and nothing lowers it (kernel messages "lambda
domain mismatch: (Pi Type2. ...) vs (Pi Type1. ...)", and "inferred Type3, expected Type1" for a `Nat_k -> Nat_(k+1)` map, both
pinned by a test). So the shift-and-add loop is unrolled in the meta-language, one level per multiplier bit: the law is
uniform in the output position and the multiplicand stream, not in the multiplier's width, and the multiplier must be a
literal. With that, `mul x 0 = 0` and `mul x 1 = x` are proved and bridged to a `mul(n)` defined in the test from
`encoding::add` and `encoding::bitwise` (the encoding has no `mul`), accepted for n = 1 to 6 (checked n = 1 to 3 in the default
tests). The reviewer's caveat was material: in both laws every shifted partial product is masked by a zero multiplier bit, so
no proof observed the shift (flipping `shl_bv`'s fill bit left the bridge tests passing; only the literal-multiplication
computation tests caught it). `mul x 2 = x + x` (`uniform/shift.rs`) closes that: it is proved uniformly in the output position
and bridged to `Pi x:Bv_n. GoodBv x -> Id(Bv_n, mul(n) x (lit 2), add x x)` for n = 2 to 4 (n = 5, 6 in the scaling test), and
flipping the fill bit of `shl_bv` or of the stream shift is now REJECTED by the bridge check itself while the old `mul x 0` and
`mul x 1` bridges still accept the mutant. The proof is not the hinted carry induction on `x + x`: `maj(a,a,c) = a` is stuck on a
symbolic carry, so a joint induction shows the shift's fold and the adder's fold for `x + x` run in step (`AD M = SH M` as states,
with `GoodBool` of the carry kept in a `Sigma` component, which puts its motive in `Sort2` and needs k >= 1), then a zero-left-operand
lemma and lemma Y for the trailing zero multiplier bits; lemma Y's `GoodBool` hypothesis had to become conditional on the position
being good. Level rule met on the way: a case split on a `GoodBool` witness admits motives into `Sort1` only, so the split is on a
`Bool0` equality lifted to the state with `rew`. `mul 1 y = y` with a SYMBOLIC multiplier was bridged three ways, to `Pi y:Bv_n. GoodBv y -> Id(Bv_n, mul(n) (lit 1) y, y)`; the first two
bridges are deleted and the third, stage-wise one is the only bridge now (`uniform/symmul.rs`, further down). The first, positionwise, bridge was tested for n = 1 to 4 in the default tests (6 and 7 in the ignored scaling test): the multiplier bits are the `GoodBv` step's variables, each partial
product `and(y_j, e_j)` stays stuck, and the proof splits on the witnesses of `y_p` and `y_j` for p < j only. It is positionwise at numerals
(not uniform in the position; the hinted "disjoint add" lemma needs shl facts at a symbolic position and was not attempted) and needs
k0 = 1, since the multiplicand is the closed one-hot stream. The fill-bit flip is rejected by this bridge for n >= 2 (at n = 1 there is no
shift). Cost: check 52 against 15 ms at n = 6 and 369 against 45 ms at n = 7 versus the per-width baseline (2-8x slower), build 1.1 s and
4.4 s against 0.06 and 0.2 s; the term grows about 4x in memory per bit and n = 8 hit the 8 GB cap (peak 9.2 GB), a cost of the
positionwise construction (a binomial tree of clones), not a kernel finding. The uniform-in-position form (once `uniform_symmul_uniform.rs`; its stream theorem is now `uniform/symmul_stream.rs`, its bridge deleted) was built too: for every good position `i`, `acc_n i = look(a_0..a_(n-1)) (lower i)`,
with no per-position case tree, from a pointwise lookup lemma (D: one induction on the position, instances for the carry staying false and
for the sum bit), a lemma that the stream shift transports a lookup (a joint induction with `Good (embed M)`, as in the carry lemmas), and
a per-stage theorem on `carry_false`; the multiplicand is the stream `look(1,0,..,0)`, convertible at every numeral to the old one, so the
`Bv_n` statement is unchanged. It was bridged for n = 1 to 4 (default tests), 5 to 9 in the scaling test. What it buys and what it does not:
the stream theorem is cheap (stage check 7 to 19 ms for n = 4 to 8, about 2 ms of build per bit) and the build and memory are far
smaller than the positionwise bridge (build 85 against 1465 ms at n = 6; peak 385 MB at n = 7 against 4.3 GB; n = 8 runs in 8 GB), but the
END-TO-END bridge check is no faster and not polynomial: 130, 736, 4238 ms at n = 6, 7, 8 (positionwise 117 and 369 at n = 6, 7; 33.6 s and
5.4 GB at n = 9, about 6x per bit). The cost is the kernel converting the statement's fixed-width `mul(n)` on stuck symbolic bits against the
stream product (at n = 8 bit 7 alone takes 2.2 s), not the proof; the term's distinct nodes are quadratic in n but its unfolded tree grows
8 to 10x per bit. The stage-wise bridge (once `uniform_symmul_opaque.rs`; now `uniform/symmul.rs`, the only bridge) avoids that conversion and the check becomes polynomial: each accumulator stage is a
closed handle `ACC_j`, `S_j` states `Id(Bv_n, ACC_j a.., T_j)` with `T_j = (a_0..a_(j-1), ff..ff)`, and `S_(j+1)` rewrites with `S_j` and then
applies a stage lemma `add T_j P_j = T_(j+1)` proved directly at the `Bv` level (one case split on the witnesses of `a_i`, `a_j` per position
`i < j`, each carry shown false by a `rew` chain), so no step converts more than one add. Bridge check 10 to 14 ms at n = 8 against 3.9 to 4.4 s
(300 to 390 times faster over two runs), then 17, 43, 133, 211, 382 ms at n = 10, 12, 16, 20, 24 (roughly n^3; peak commit 257 MB at n = 8, 640 MB
at n = 24); the one remaining conversion, `mul(n) (lit 1) (tuple a)` against `ACC_n`, takes 0.3 to 3.3 ms at n = 4 to 8 and 163 ms at n = 24. The
build is not cheaper (300 against 128 ms at n = 8, 20 s at n = 24) and the unfolded term still doubles per bit, so the check is cheap
because the kernel shares subterms. The fill-bit flip is rejected at the stage that shifts (with fill true, `S_1` checks and `S_2` to `S_4` are rejected), not only
at the final conversion. Against the per-width proof of the same statement (a case split on all n bits for every output bit, 2^n leaves per bit) it wins
from n = 8 on, in the check and in build plus check (one contended run, run `2026-11-01-opaque-vs-base-b`: CPU 77% with a game running, the
timed form was refused, so read ratios, not milliseconds): check 4.8 against 2.3 ms at n = 4, 32 against 9.8 at n = 6, 187 against 16 at n = 8,
547 against 28 at n = 9, 1357 against 33 at n = 10 (2x growing to 41x); build 8 against 40 ms at n = 4, 139 against 200 at n = 6, 1.5 s against
0.48 s at n = 8, 15.4 s against 1.1 s at n = 10, so the baseline is cheaper to build and check below n = 6 or 7 and the bridge wins above, the
gap growing about 2.5x per bit. The first width-uniform route that beats the per-width proof, for this law. On Church streams commutativity, a symbolic multiplicand with a symbolic multiplier, and any law
uniform in the multiplier's width stay unbuilt (the W-built index below reaches the last two). Bridge check against the per-width baseline for `mul x 2 = x + x` (one run): 5.6 against
3.6 ms at n = 4, 14.4 against 14.2 at n = 5, 68 against 55 at n = 6, so roughly even there (build 21 to 232 ms against 0.5 to 48).
For the older laws, bridge against per-width baseline (one run): `mul x 1 = x` 9.1 against 3.4 ms at n = 4 and 287 against 69 ms at n = 6 (the reviewer's rerun: 1435 against
375 ms); `mul x 0 = 0` against a baseline that is just `refl`, so no fair comparison. A first accumulator that repeated each operand
three times grew as 3^j (14.6 s to build at n = 4) and hit the 8 GB cap at n = 5; sharing the accumulator as a closed term made the build linear.

**`tree_encoding`'s reachability guard never added a proof, and is deleted (2026-11-07; runs `2026-11-07-p1-inv-count-2`, `2026-11-07-p1-reach-ab-3` and `2026-11-07-q1-guard-deleted`).** Its second `moore_encoding` attempt, over the reachable carry states, proved laws conditional on a reachability invariant (added in 76d4f18). Refinement stops at a stable partition, so `try_encoding` cannot fail on Moore classes, and whether two start states share a class depends only on the states they reach. So the attempt over all states finds whatever the restricted one does. The argument is read from the code, not proved. Evidence for it: in the lib tests the restricted attempt never ran (325 passed, 47 ignored not run; the branch was reached 3 times, each with every state reachable). Forced directly on enumerated pairs with an unreachable state (width 4, two operator levels, at most 400 pairs per class, about 84 million untried), the two attempts agreed on all 103418: both found 94975, both missed 8443. `lt x 0 = lt y 0` and `lt (x+y) x = lt (x+y) y`, which do have unreachable states, pass the first attempt. The check is at `git show cdbf3b3:crates/church-bv/src/machine_reach_tests.rs`. If a law ever needed the invariant, the search would return no encoding rather than a wrong proof.

**The level wall is Church's, not the kernel's: a W-built index folds into its own streams (spike, 2026-11-07;
`crates/church-bv/src/uniform/wnat.rs`; runs `2026-11-07-o1-wnat` and `-2`).** The "single fold is ill-typed" result above holds for
Church numerals only. A Church `Nat_k` folds only into `Sort k`, and the stream adder raises its output one level, so a stream
accumulator is a missing fixed point: a step would need `Bits(a+1) = Bits(a)`. `WRec`'s motive has no such cap. The index is
`N := W(Tag, fst)` with `Tag := Sigma X:Sort1. Sigma m:Maybe X. GoodMaybe m`: a bare Church tag gives a step no way to use its
child function, so the tag carries the witness and the branch needs no dependent motive. `Empty` and `Unit` are derived (no
postulate), `N` and `Bits := N -> Bool0` both sit in `Sort2`, and `add : Bits -> Bits -> Bits` raises no level. The multiplier is
one `WRec` with a stream-function motive, in Horner form: `mul (succ p) x y = (x & y_0) + shl (mul p x (shr y))`. No kernel change.

Every stage passed (times from the two runs at 71-76% CPU, one live GPU lease):
- Types: `add`, `shl` and `mul : N -> Bits -> Bits -> Bits` typecheck at the stated types.
- Computation: 8 closed 3-bit products match by `def_eq` at every position through bit 7; the shift's fill-bit mutant gets all 4 tested products wrong.
- `Pi m y i. mul m 0 y i = false`, in 1.2-1.8 ms.
- `Pi x y. good x -> good y -> Pi i. add x y i = add y x i`, with real carries, in 0.6-1.0 ms (single reads, no lease).
- `Pi m x y i. mul m (shl x) y i = shl (mul m x y) i`, in 2.5-3.0 ms: symbolic width, multiplicand and multiplier, no goodness hypothesis at all.
  The partial product masks with the operand first, `and(x j, y_0)`, so `shl x j = false` makes it false by computation.

Controls: each law's proof is rejected against a false statement, and the shift law's two-sided theorem, read at closed numbers,
reduces to the true bit of `2xy` for 4 products at 9 positions, with the flipped bit rejected.

What this does not show. Nothing consumes these laws: `mul` is not among the loop's eight operators, so this moves no served rule
and no mining cost. It moves one decision: a kernel `NatRec` (spec part 2 §53, option 4) is no longer the only way to a law uniform
in the multiplier's width. The laws are about streams; no bridge to `Bv_n` exists, and `width.rs`'s lookup does not carry over, because its
`Sigma(b, GoodBool b)` state sits in `Sort2` and `Maybe`'s `C` is `Sort1` (a limit on a fold's state, not on a law: "One generator proves stream laws at all widths", below). `mul` commutativity is not close (inference, not tried):
`mul m x y` reads `m` bits of `y` and all of `x`, so the two orders agree in general only below position `m`, which needs an order predicate on trees to state, and `mul` must distribute over `add`.

The tree is not canonical (`nothing` under an inhabited `X` is a second zero, `X` may branch, `succ` is not injective), so `N` has no
general induction. `GoodMaybe`'s motive sits in `Sort1` and sees `m` but not its witness, so a proof states its goal reduced at the
tag's `m`. That covers every statement that reads a tree through its tag, which is all a stream function can do; it is why `ind` in
`wnat.rs` takes the statement in reduced form. A hand proof writes that form itself; `wfold.rs` builds it from the machine.

**One generator proves stream laws at all widths, and the `Sort3` limit was never there (spike, 2026-11-07; `crates/church-bv/src/uniform/wfold.rs`; runs `2026-11-07-q2-fold-5` and `2026-11-07-q2-fold-final-2`).** A stream law here is a pair of terms with no `shr1` or `mul`, and `lt` only at the root of both sides or neither. `Law::new` reads two terms through `Machine` and `moore_encoding`, as `tree_proof` does at one width, and `Law::proof` builds the theorem with no per-law code: one goodness induction per carry, the per-side case lemmas, one induction on the phi agreement, then the output. The statement is `Pi x.. good x.. i. l i = r i` over `wnat.rs`'s own `add`, `shl` and a `sub` built from `carry`; a root `lt` is its borrow stream (its value at `i` compares the low `i` bits), and the width-`n` result is its value at `n`.

The expected limit came from putting goodness in the fold's state: `Sigma(c, GoodBool c)` sits in `Sort2`, and a tag splits only into `Sort1`. Nothing needs that state. A carry's goodness is its own induction with `P` bound by `ind`'s `pre`, so what crosses the tag is `P c`, in `Sort1`, and the phi agreement is a `Sigma` of `Id`s, also in `Sort1`. `GoodMaybe` stays as it was. What the W index does contribute is the nesting: `add (add x y) z` is one level, because an adder's output is a stream of the same type. Whether the Church index could carry this proof is untested. It could not state nested `add`s at one level, so it would need a statement about one machine's tuple of carries (inference).

Results:
- `(x + y) + z = x + (y + z)`, the first all-width proof of `add` associativity, in 16 ms (single reads here and below, untimed runs).
- 17 more laws in 0.8-36 ms, including `(x+y)+(z+u) = (x+z)+(y+u)`, `sub(x, x) = 0`, `sub(x, y+z) = sub(sub(x, y), z)`, `(x^y) + shl(x&y) = x + y`, `shl(x+y) = shl x + shl y`, distributivity of `and`, and five `lt` pairs, two of them not constant (`x < y = ~y < ~x`).
- Sweep: terms of two operator levels on `x`, `y`, `0`, `-1` with `add`, `sub`, `and`, `or`, `xor`, `shl1`, and `lt` of any two one-level terms, each paired with the first different term of the same width-4 table (an `lt` only with an `lt`): 45677 pairs, 45621 with an encoding, every one of whose proofs the kernel accepted, in 1752 s, peak commit 5044 MB. The other 56 are all `lt` pairs that differ at width 1 (`0 < -1 + -1` holds at width 4, not at width 1), so they are not laws at every width; the test checks that each pair with no encoding differs at some width from 1 to 6. This pairs each term with one representative, not every two terms of a class.

Controls: the associativity statement is `def_eq` to one written by hand from `add`; its proof is rejected against `x + (y + y)`; flipping one table bit in the encoding is rejected; `x + y = x` and `x < y = y < x` have no encoding, and the proof of `x < y = ~y < ~x` is rejected against `x < y = y < x`. The streams, read at 5 closed operand pairs, give the 3-bit words of 8 terms by `def_eq`, and a root `lt` at every position `p` compares the low `p` bits. The associativity theorem, applied to constant streams with their goodness witnesses, gives bit 2 of `(7 + 7) + 0` and rejects the opposite bit, so its hypotheses hold of real streams.

The review of this work found a wrong law the kernel could not catch. `Machine::step` then read an `lt` below the root as `sub` (an `lt` now outputs its borrow, which a parent would misread as a word), so `add(lt(x, y), z) = add(sub(x, y), z)` got an encoding and an accepted proof: a true statement about subtractor streams, false of the terms. No earlier test or sweep had a nested `lt`. `Machine::parse` now builds no machine for one, so neither encoding nor `side` can read it, and `moore_encoding` returns `None` for a root `lt` against a word (both 2026-11-07). A proof here checks a statement about the streams `side` builds, so what ties a law to its terms is that reading, tested only by the closed-stream control above.

Where a sweep's time goes (1-in-97 sample, 469 proofs, run `2026-11-07-v2-build-profile`; 21 s under samply, phase timers 0.19 s encoding, 21.2 s building, 3.6 s checking in an untimed read). Of busy samples, `Law::proof` is 83% and the kernel check 10%. In the build, `by_cases` is 46% (its case trees), lowering to kernel terms (`width::ex`, `comp`) 31% of the whole, of which interning in `mk` 23%; `wnat::ind` 23%, `table` 13%, `Law::closed` 11%. Allocation, cloning and drops of the named tree `T` take about a third of self time (`ptr::write` 13%, `mi_free` 7%, `clone` 5%, drops 5%, malloc 6%). A `T` is a tree with no sharing, so each repeated table, step and motive is built, copied and lowered again, where the kernel's interned `Expr` (what `tree_proof` builds on) shares them; the build cost tracks the unshared size.

What this does not show. There is no bridge to `Bv_n`, so no hand-written family can go yet: `bitwise.rs`, `shift.rs` and `symmul.rs` each prove a `Bv_n` statement through theirs. The families' stream theorems are about Church-indexed streams, and nothing outside `uniform/` uses any of them. `shr1` and `mul` are outside, neither being a left-to-right machine, and so is `lt` below the root. That every stream law gets a proof is not itself proved: `moore_encoding` finds an encoding for any two equal machines, and the sweep samples the rest of the path. The generator names at most 4 variables and 12 case bits.

Related systems get width-generality from integers mod 2^w (Lean `BitVec`, Coq bbv, the parametric bit-vector SMT work); none retrieved
in the 2026-11-07 survey proves it bit-serially, so a bit-level fold on a kernel with no built-in induction looks new (inference; Isabelle
and Hydra's exact check were not verified). The same survey's other two candidates are parked in `PARKED.md`, under the goal D entry.

**Compiling hot transformations, with learnable compilations: two falsifiers (probes, reverted, no patch kept,
2026-10-14).** The goal: the kernel compiles hot transformations natively, and the compilations are learned, not fixed.
Of three ways to trust compiled code (trust the compiler, as `native_compute` does; a certificate per output; prove each
compilation step once against a small fixed target semantics), the third gives one object kind and one fixed trusted
piece: optimisations are term-to-term rules, lowerings are term-to-IR rules proved against an IR semantics stated in the
kernel, a hot transformation is compiled by lowering its rule's matcher and builder, and learning a compilation is mining
lowering rules by target cost, with hotness from rule-use counts (not built; precedents from memory, not re-checked:
Alive, STOKE, Souper). Two cheap tests of its base:

1. *Can lowering templates be stated and proved as kernel laws?* Yes. `tests/lowering_law_probe.rs` (deleted) stated a
   typed-stack IR as a shallow kernel semantics: `Code = Pi S:Sort0. S -> Sigma(Int, S)` (runs on any stack, pushes one
   Int) and `Spec(c, m) = Pi S. Pi s:S. Id(Sigma(Int,S), c S s, pair(m, s))`, with `Int`, `add` and `sub` postulated as
   `proof.rs` does. Checked by the kernel: Lit (`Spec(lit n, n)`, by `refl`); Add (`Spec(c1,m1) -> Spec(c2,m2) ->
   Spec(add_template c1 c2, add m1 m2)` for arbitrary code `c1`, `c2`, by `cong1` and `trans_proof`); and If (a
   bool-pushing `cc`, then `ct` or `ce`, by `cong1`, `cong_n`, `sym` and `trans_proof`). Negative controls were
   rejected: the Add template lowering to `sub` under the same statement, and If with its branches swapped. A concrete
   term's compiled code (`add(lit k1, lit k2)`) was proved by applying the two template laws, with no per-term search.
   One obligation surfaced: If needs its condition to be *natural* (`f (b x y) = b (f x) (f y)` for every `f`), which a
   Church boolean does not give for free; `tt` and `ff` are natural by `refl`, so each instruction that pushes a
   condition (`lt`, `eq`) must prove it in its own spec. Limits: the IR semantics is a model in the kernel, as `denote` is,
   so the step from it to wasm stays trusted; that is the fixed piece this design keeps. All checks took under 0.01 s.
2. *Does scoring by compiled cost pick different rules than scoring by M?* Yes, mostly, and the two objectives conflict
   on cmp3d. A `RULEMINER_LAWW` weight (default 1000, the weight of a fixed law and of the guard laws) was set to 0, so a
   rule scores only by the cut in the stragglers' normal-form size (`measure`: operator weight times 16 plus variable
   occurrences, a proxy for a stack IR's instruction count, one instruction per node; not counted from `lower_wat`). Ref
   loops on phase 0 (`LOOP_MODE=ref`, B=150, K=4, `RULEMINER_FAST=1`, `CHECK_FAST=1`, 2 threads; each loop 2-5 s):

   | | rules | shared | stragglers fixed | serve M | size cut |
   |---|---|---|---|---|---|
   | add3, scored by M | 14 | 2 | 87 of 87 | 1 | 1075 |
   | add3, size only | 8 | | 34 of 87 | 83 | 1075 |
   | cmp3d, scored by M | 27 | 5 | 250 of 264 | 16 | 457 |
   | cmp3d, size only | 24 | | 171 of 264 | 120 | 4205 |

   On add3 both reach the same total size, and the M-scored library also fixes every straggler: size-only stops when no
   rule cuts size, before the zero-cut rules that close proofs. On cmp3d, seven of the M-scored rounds grow normal forms
   (1803 in total) to fix 41 laws, so the M-scored library cuts 9x less size; the size-only library leaves 7.5x more
   machine proofs. Learning by compiled cost is therefore not subsumed by today's miner, and one miner can serve both
   with one objective of two weighted terms (proof cost and compiled cost) rather than two miners. The mul and shl
   families gave no test: under today's built-in rules mul (`MULMINER_MAX=5`) has 0 stragglers of 50 laws, and shl
   (`RULEMINER_LAWS=300`) has 5 stragglers of 305 laws and 0 oriented candidates.

**The fixed-law weight between 1000 and 0 (probe, reverted, no patch kept, 2026-10-14).** The same ref loops with
`RULEMINER_LAWW` at 1000, 300, 100, 30, 10, 3 and 0 (seconds per loop; the 1000 and 0 rows repeat the runs above
exactly). "Fixed" is stragglers fixed in the mine; serve M is on the same 600 (cmp3d) or 204 (add3) laws, so both are
in-sample, one phase, one salt:

| weight | cmp3d rules | fixed of 264 | serve M | size cut | add3 rules | fixed of 87 | serve M | size cut |
|---|---|---|---|---|---|---|---|---|
| 1000 | 27 | 250 | 16 | 457 | 14 | 87 | 1 | 1075 |
| 300 | 28 | 250 | 16 | 457 | 14 | 87 | 1 | 1075 |
| 100 | 30 | 253 | 14 | 3740 | 14 | 87 | 1 | 1075 |
| 30 | 32 | 249 | 17 | 4044 | 16 | 85 | 3 | 1075 |
| 10 | 36 | 228 | 39 | 4469 | 12 | 82 | 5 | 1075 |
| 3 | 32 | 244 | 20 | 4249 | 13 | 82 | 5 | 1075 |
| 0 | 24 | 171 | 120 | 4205 | 8 | 34 | 83 | 1075 |

At weight 100, cmp3d's library is better on *both* terms than at 1000: 3 more stragglers fixed, serve M 14 against 16,
and 8.2x the size cut. On add3, 100-1000 give the same library. So the greedy miner at 1000 is not M-optimal either:
rules that grow normal forms to close a proof now block cheaper closures later. Not yet a default change: it is
in-sample, and an `own` loop on phases 1-3 (held out) at weight 100 against 1000 is the test (not run). Below 100, M
degrades; the curve is not monotone (10 is worse than 3 on cmp3d).

**Formalizing the target machine (survey, no code, 2026-10-14).** What the kernel would have to state to prove
lowerings against the real target, and what exists. What `lower_wat.rs` emits today (by counting its instruction
strings): i64 `add sub mul div_s rem_s lt_s le_s eq or shl shr_u const extend`, `local.get/set/tee`, `i64.load/store`
(closure environments in linear memory), `call`, `call_indirect` (unknown calls through a table), `block`, `br`, `if`.
Today the IR-to-WAT lowering is trusted, validated per compilation by the decompiler (a hash check, IR to term) and
per template by differential tests against `eval.rs` at edge values (`docs/superpowers/specs/2026-09-23-jit-ir-design.md`,
steps 2-3).

Options, ranked by end-state design:

| | Option | End state | Risks and open questions |
|---|---|---|---|
| B | Deep embedding of the emitted wasm subset in the kernel: instructions as data (a `W` type), an interpreter by `WRec` over code, `i64` as the loop's Church bitvectors at width 64 | One semantics for both systems: the ops both have (`add`, `sub`, `or`, unsigned compare) are the same functions at n=64, so a mined law over them applies to compiled code directly (`mul`, `div_s`, `rem_s`, `eq` and shifts by a variable amount still need defining over bits), and signed `lt_s` is definable from unsigned `lt` (flip the sign bits). Lowering rules are term-to-instruction-list rules, proved once against the interpreter; `lower_wat`'s templates become data the kernel checks, so `lower_wat` and the decompiler leave the trusted base (wasmtime stays) | Proof cost at n=64: `add x 0 = x` is gated at under 400 k nodes at n=64 and about 3x per doubling (`encoding.rs:599-612`), and the universal lemma checks at n=64 (`encoding.rs:1001`), but mined rules at n=64 are not measured. Traps (`div_s` by zero, `MIN / -1`) need a partial result type. Memory and `call_indirect` need a heap and a table model; a straight-line i64 fragment first (no memory) is an additive stepping stone |
| A | The shallow typed-stack semantics of the probe above, with `Int` postulated | Lowering laws over a model; the model-to-wasm step stays trusted | Values have no bits, so the loop's laws do not connect without a postulated bridge, and instructions are kernel functions, not data, so a lowering cannot be compared with `lower_wat`'s output. A probe, not an end state; B restates its three laws deep |
| C | Import a mechanized Wasm semantics: WasmCert-Coq (Wasm 2.0 per its author's 2025 thesis), WasmCert-Isabelle, or SpecTec (the spec written once; its generated interpreter passes the official 2.0 test suite, PLDI 2024) | Fidelity to the standard without hand-writing it | Different logics (Coq's CIC, Isabelle/HOL) from this kernel's small MLTT; SpecTec's prover backends are prototypes (an IL-to-Coq translator for Wasm 1.0; Lean and others as future work, per a Dagstuhl abstract and ECOOP 2025). Rejected as the kernel's semantics; kept as B's differential oracle (run SpecTec's interpreter or the official test suite against B's interpreter on the emitted subset) |
| D | Go below wasm: a native ISA semantics (Sail models of Arm-A and RISC-V, with Isabelle, Coq and HOL4 output, and a Lean target used by sail-riscv per a 2026 project script) | Removes wasmtime and Cranelift from trust | The ISA models are large and the native code is Cranelift's, not ours. Crocus (ASPLOS 2024) already verifies Cranelift's ISLE lowering rules against aarch64 semantics with SMT, finding a 9.9-severity CVE among known bugs: evidence that lowering-as-rules works at production scale, not a part to rebuild. Parked |
| E | SMT-checked lowering rules (Crocus, Alive style) in place of kernel proofs | Fast checks | A second checker, which the one-kernel design avoids. Usable as a screen before the kernel proof, as the width 1-6 screen is for laws |

B is the only option that removes concepts: the JIT's postulated `Int`, `proof.rs`'s `denote` model of the compiler
and the decompiler's role as the trusted check all collapse into one interpreter over bitvectors that the loop already
uses. Cheapest falsifier, additive: state `i64.add` and `i64.lt_s` over width-64 Church bitvectors, re-prove the
probe's Add and If templates deep (instruction lists interpreted by `WRec`), and time the proof of one mined cmp3d rule
at n=64 against n=4. If the n=64 rule proof is out of reach, B needs width-generic proofs first. Run in part, with
the shallow templates rather than deep ones: see the next paragraph.
Sources: [Crocus](https://cs.wellesley.edu/~avh/veri-isle-preprint.pdf), [WasmCert](https://hal.archives-ouvertes.fr/hal-03353748),
[SpecTec](https://pldi24.sigplan.org/details/pldi-2024-papers/64/Bringing-the-WebAssembly-Standard-up-to-Speed-with-SpecTec),
[Iris-Wasm](https://pldi23.sigplan.org/details/pldi-2023-pldi/46/Iris-Wasm-Robust-and-Modular-Verification-of-WebAssembly-Programs)
(a separation logic over WasmCert-Coq, for programs rather than compilers), [Sail](https://www.cl.cam.ac.uk/~pes20/sail/popl2019.html),
[sail-riscv Lean script](https://raw.githubusercontent.com/Verified-zkEVM/evm-asm/main/scripts/regen-sail-model.sh).

**Mined rules at width 64, and compiled programs proved equal from them (probes, reverted, no patch kept,
2026-10-14).** Two probes in `crates/church-bv/src/rewrite.rs` at e49847e, on the 37 rules of cmp3d's own library
(`cmp3d_own_rules.txt` without its `OVER` lines). Machine load about 30% CPU at the start of each; Defender real-time
protection off.

*Width.* Every rule's law (`prove_rule`) builds and checks at n = 4, 8, 16, 32 and 64:

| n | check, all 37 (s) | slowest rule (s) | mean proof nodes |
|---|---|---|---|
| 4 | 2.96 | 1.12 (includes warm-up) | 5306 |
| 8 | 1.18 | 0.08 | 9860 |
| 16 | 3.32 | 0.23 | 18987 |
| 32 | 10.89 | 0.74 | 37319 |
| 64 | 40.36 | 3.59 | 74294 |

Nodes about double per doubling of n (linear); check time grows about 3.7x from 32 to 64. The largest proof at n=64
has 175544 nodes and checks in 3.5 s. So this library needs no width-generic proofs to reach wasm's i64; the survey's
question "is the n=64 rule proof out of reach" is answered no, for these rules.

*End to end.* Both sides of each rule compiled with the stack templates (shallow: `Code = Pi S. S -> Sigma(V, S)`, as
in the first falsifier above, now with `V` the Church words of width n instead of a postulated `Int`), each side's spec
proved by composing the Lit and Bin template laws, and the goal `Pi S s. Id(c_l S s, c_r S s)` proved by
`trans(spec_l, cong(push, law), sym(spec_r))` from the rule's own kernel law. The Bin law needs an output value type:
`lt_u` returns a one-bit word, not an n-bit one (as `i64.lt_s` pushes an i32), so the law is stated once per output type
(`Bv_n`, `Bv_1`); each checks in about 1-2 ms. Results, 37 rules:

| n | equivalences proved | spec proofs by template laws (s, all) | same spec by `refl` | equivalence check (s, all / slowest) | mean / max proof nodes | mean code nodes |
|---|---|---|---|---|---|---|
| 4 | 37 | 0.11 | 37 | 0.85 / 0.07 | 6321 / 13903 | 1155 |
| 64 | 37 | 0.43 | 37 | 68.2 / 10.2 | 81317 / 183582 | 11569 |

The equivalence check includes checking the embedded rule law, which alone is 40.4 s of the 68.2 at n=64 (width table).
Controls: with the rule law replaced by `refl`, all 37 equivalences are rejected; each Bin law is rejected against the
other output type's statement. Two traps met on the way, worth knowing for any code that reuses mined laws: the laws
refer to shared lemmas bound as parameters of the thread-local `PARAMS` postulates (`shared_lemma`), so they check
only in that scope (in a fresh `Postulates` the check fails with "free parameter escaped its scope"); and a pushed
`lt` value has `Bv_1` as its inferred type, so pairs need the output type explicitly.

*What this changes in the survey.* The step that option B's first falsifier was to measure, mined rule proofs at the
target's width, is cheap, and a mined law transfers to compiled code through one congruence, with per-compile spec
proofs from the template laws costing well under a second. Not shown here: signed `lt_s` (the miner's `lt` is
unsigned) and any op outside the loop's eight; the If template is the next paragraph. On deep syntax: a `W` type of
instructions is costly in this kernel. `NatPostulates` gets a computing tag through postulated computation axioms
(`child_ty_true_eq`, `bool_rec_true_eq`, `crates/tatic-kernel/src/postulates.rs`) and a transport per constructor, which would
grow the trusted base; a tag carrying its own witness computes with no postulate ("The level wall is Church's", above), but
only two-constructor tags are tested, and a whole instruction set on it is unmeasured. Two ways around it: keep the semantics shallow and trust
only the printer from the template-built instruction list to WAT text, or Church-encode instruction lists; the second
is tested two paragraphs down and works.

**The If template with a compiled `lt` condition, and instruction lists as Church-encoded data (probes, reverted, no
patch kept, 2026-10-14).** Both on a fresh cmp3d library: a ref loop at e49847e (`LOOP_MODE=ref FAMILY=cmp3d
RULEMINER_FAST=1 CHECK_FAST=1`), 27 rules, 24 of them `lt` rules. (The 37-rule list of the paragraphs above was a
scratch copy of a run directory that no longer exists, and was deleted by mistake, so the two libraries differ.)
Machine load 21-29% CPU; Defender real-time protection off.

*If.* The first falsifier's If needed its condition at the stack's universe (`b (Sigma(V,S)) ..`, with naturality).
That route is closed for the loop's words: their bits are Church booleans in Sort0 and stacks live in Sort2, and the
kernel has no large elimination, so a bit cannot choose between two stacks. What a bit can choose is a bit: a
word-level `select c x y` built from the existing `mux` gate per bit is definable and checks (on literal words it
returns the named branch, and not the other). So the If template pops the one-bit condition, runs both branches on
the rest of the stack and pushes `select w v_t v_e`, which is what wasm `if` computes when both branches are pure;
control flow proper (only one branch runs, effects) is not modeled. Its law, `Spec(c_c,m_c) -> Spec(c_t,m_t) ->
Spec(c_e,m_e) -> Spec(if c_c c_t c_e, select m_c m_t m_e)`, is three congruences and checks in about 1-2 ms; against
the swapped-branch statement it is rejected. For each `lt` rule `l -> r`, `if l then x else y` and `if r then x else y`
(branches the rule's first two words) were compiled and proved equal from the rule's law:

| n | equivalences proved | spec proofs (s, all) | equivalence check (s, all / slowest) | mean / max proof nodes |
|---|---|---|---|---|
| 4 | 24 of 24 | 0.09 | 0.53 / 0.04 | 6625 / 7694 |
| 64 | 24 of 24 | 0.32 | 29.3 / 1.86 | 78953 / 94034 |

With the rule law replaced by `refl`, all 24 are rejected. Not shown: an If whose branches are themselves compiled
terms, and `if true then a else b = a` for a symbolic `b` (with Church tuples `select` nests both branches'
eliminations, so that holds by computation only for literal `b`; it would need `GoodBv`).

*Instruction lists as data.* A naive Church list does not work: `fold (l1 ++ l2)` is `fold l2 . fold l1` only by
induction on an abstract `l1`. Two choices make it hold by beta. A program is encoded by its end stack type,
`Prog S T = Pi F:(Sort2 -> Sort2). F T -> (Pi A B. Instr A B -> F B -> F A) -> F S`, so appending puts `p2` where `p1`'s
nil is (`p1 ++ p2 = \F n c. p1 F (p2 F n c) c`). And a program means its continuation-passing run,
`M p R k = p (\A. A -> R) k (\A B i rest a. rest (I i a))`. Then `M (p1 ++ p2) R k` is `M p1 R (M p2 R k)` and checks by
`refl` for abstract `p1`, `p2` (about 1-2 ms). An instruction is an indexed Church sum,
`Instr A B = Pi G. (Pi A. V -> G A (V,A)) -> (Pi A. (V->V->V) -> G (V,V,A) (V,A)) -> (Pi A. (V->V->V1) -> G (V,V,A) (V1,A)) -> G A B`
(push a word, a word op, a compare), interpreted by its eliminator at `G A B = A -> B`; all of it lives in Sort3, and
nothing is postulated. With the spec stated over every continuation, `Spec(c,m) = Pi S R k s. Id(R, M (c S) R k s, k (m,s))`,
the Bin law for `c1 ++ c2 ++ [bin op]` is two transitivity steps with no congruence; each output type's law checks in
about 5-12 ms and is rejected against swapped operands. Each rule's two sides, compiled to instruction lists, proved
equal from its law (`cong` of the continuation-after-push on the law):

| n | equivalences proved | compile + spec + equivalence checks (s, all / slowest) | mean code nodes |
|---|---|---|---|
| 4 | 27 of 27 | 0.96 / 0.06 | 1390 |
| 64 | 27 of 27 | 36.3 / 2.19 | 11603 |

With the rule law replaced by `refl`, all 27 are rejected (n=4). And the code is data: run on free `F nil cons`, the
weak head normal forms of every compiled side are `cons A B i rest` down to `nil`, and each instruction on free
`G c0 c1 c2` is `c_k A payload`, so a printer walks the list without unfolding payloads. On all 54 sides at both
widths it reads back exactly the term's postfix order (rule 0's left side: `push x, push y, add, push z, sub`). A
printer that fully normalized the program instead stalled at n=64: normalizing the ripple-carry op payloads unshares
them into a tree.

*What this changes in the survey.* Option B's end state is reachable without a `W` type or new axioms: instructions
are kernel data a printer reads, template laws over them are cheap, and mined laws transfer to compiled instruction
lists at width 64. The trusted step that is left is the printer from the instruction list to WAT text (a syntactic
map), plus wasmtime. Still open: control flow and memory (control flow is tried in the next paragraph; `if` with effects, `block`/`br`, `i64.load/store`,
`call_indirect`), the wasm ops the loop lacks, and whether lowering rules can be mined over this encoding.

**Control flow over Church instruction lists, with answers in Sort0 (probe, reverted, no patch kept, 2026-10-14).**
The `select` If above runs both branches, which is wrong once a branch can loop. Real `if` needs a bit to choose
between two runs, and a bit eliminates only into Sort0. Without a primitive Bool or sum type, the option tried here
moves the answer instead: the meaning `M p N R k z` takes the answer type `R : Sort0`. One gap remains: a one-bit
word `Pi X:Sort1. (Bool0 -> X) -> X` opens only at Sort1, and the kernel has no cumulativity. It is closed by
opening the word at `Lift R = Pi Y:Sort0. (R -> Y) -> Y` (in Sort1) and projecting at `Y := R`. So
`choose w x y = w (Lift R) (\c Y g. g (c R x y)) R id`, and no kernel change is needed. Programs gain two
constructors:
- `if : Pi A. F A -> F A -> F (V1,A)`, taking a then-rest and an else-rest;
- `loop : Pi A. (F A -> F A) -> F A`, a body over its own label, where `br L` is the label used as the rest.

Instructions gain `dup`. `if` means "pop the bit, `choose` a rest". `loop` unrolls its body `N` times (`N` a
Church numeral, the fuel) and answers `z` when the fuel runs out. Specs quantify over `N` and `z`.

Results, on the same 27-rule cmp3d library:
- **Append** still composes by `refl` for abstract programs.
- **Bin laws** check in about 10-25 ms at n=4 and n=64, and are rejected against swapped operands.
- **The If law,** `Spec(c_c,m_c) -> Spec(c_t,m_t) -> Spec(c_e,m_e) -> M (c_c ++ if c_t c_e) N R k z s = choose m_c (k (m_t,s)) (k (m_e,s))`,
  checks in 14-28 ms (two transitivity steps and two congruences). It is rejected against swapped branches.
  Its right side is a case split rather than one pushed word: an If is not an operand of a later Bin law. Code after
  the If lands in `k`, so it is duplicated into both arms, as in symbolic execution.
- **Rule transfer.** For each `lt` rule, `if l then x else y` was proved equal to `if r then x else y` from the
  rule's law:
  - 24 of 24 at n=4, 1.13 s for all;
  - 24 of 24 at n=64, 27.7 s for all.

  With the law replaced by `refl`, all 24 are rejected at n=4. The same control at n=64 hit the 4 GB guard on its
  first rule, so it was not measured: rejecting the false conversion normalizes two 64-bit words.

Concrete runs were checked by `refl` against both answers:
- `loop L { dup; push 1; lt; if (exit) (push 1; sub; br L) }` from 3 gives `k(0, rest)` with fuel 4 and 50, and
  times out (`z`) with fuel 3. From 0 with fuel 1 it gives `k(0, rest)`.
- `if lt(a,b) then loop L {br L} else push 7`, with fuel 1000, gives `k(7, rest)` for `lt(1,0)` and `z` for
  `lt(0,1)`. Only the taken branch runs.
- All programs typecheck.

These concrete checks hit a reduction wall below n=48:

| n | 8 | 12 | 16 | 24 | 32 | 40 | 48, 64 |
|---|---|---|---|---|---|---|---|
| countdown from 3, fuel 4 (s) | 0.02 | 0.08 | 0.24 | 1.14 | 3.5 | 7.6 | over 4 GB within ~10 s |

The time grows about n^3.5-4 up to n=40, then memory blows up. This is the same unsharing of ripple-carry terms
that stalled the full-normalize printer. It is a limit of evaluating concrete words by kernel reduction. It is not a
limit of the laws: the laws and the rule transfer stay at n=64. (Lifted by a kernel change the same day; see
"Closed function values are reduced once" below. Countdown at n=64 now takes 15 ms.)

Machine load: 51% CPU before the rule runs and 24% after them; Defender real-time protection off.

Not tried:
- memory (`i64.load/store` as a store threaded on the stack, with load-after-store needing `eq_bv a a = true`);
- a loop law (an invariant over fuel);
- nested Ifs as operands.

*What this changes.* Control flow where only the taken branch runs, plus fuelled loops, is expressible and provable
with no kernel change and no postulate. The costs:
- answers are confined to Sort0;
- specs are observational (`k` and `z` are quantified);
- an If composes only through the continuation;
- concrete evaluation at wide widths needs sharing in reduction (or the JIT itself) rather than raw beta.

**Memory and a loop law over the same encoding (probe, reverted, no patch kept, 2026-10-14).** Memory sits outside the
operand stack, as wasm's linear memory does. It is the CPS machine's state, `Mem = V -> (V -> R) -> R` (Sort2), and
`F A = A -> Mem -> R`. Two more program constructors:
- `store : Pi A. F A -> F (V,(V,A))` pops the value, then the address, and continues with
  `upd a v mu = \b k. (eq a b) R (k v) (mu b k)`. `eq_bv` gives a Bool0, which eliminates at `R : Sort0`.
- `load : Pi A. F (V,A) -> F (V,A)` pops an address and runs `mu a (\w. rest (w,s) mu)`.

Specs now quantify over the memory: `Spec(c,m) = Pi S N R k z s mu. Id(R, M (c S) N R k z s mu, k (m,s) mu)`.

Store-to-load forwarding at a symbolic address needs only `eq a a = true`.
- **That lemma** is `Pi a. GoodBv a -> Id(Bool0, eq_bv a a, true)`. The motive is in Sort1, since `Id` lives in its
  type's universe, so it goes through `lift_good`. Per bit, `GoodBool a_i` gives `not(xor a_i a_i) = true`, and two
  congruences per bit fold the `and` chain down to `true`, so the proof is linear in n. The kernel has no eta, but
  `and(true, true)` computes to `true`.
- **The law** is `Spec(c_a,a) -> Spec(c_v,v) -> eq a a = true -> M (c_a ++ c_a ++ c_v ++ store ++ load) s mu = k (v,s) (upd a v mu)`:
  three Spec steps, a reduction, and one congruence on the `eq` premise.
- **A use:** `push a; push a; push v; store; load` for symbolic `a`, `v` with `GoodBv a`, proved from the law, the
  push specs and the lemma.
- **Concrete:** after `store 5@3; store 9@4`, a load from 3, 4 and 6 gives `k(5)`, `k(9)` and the untouched
  `mu 6 ...` by `refl`. Literal `eq` computes.

**The loop law** is fixpoint induction over fuel. Church numerals have no induction, so fuel carries a
`GoodNat N = Pi P:(Nat -> Sort2). P 0 -> (Pi j. P j -> P (S j)) -> P N` hypothesis: parametricity as a hypothesis,
the same idiom as `GoodBv`. A loop body is `Pi F. F A (label) -> F B (after) -> handlers -> F A`. With
`Good f = Pi s mu. I s -> Q (f s mu)`, for an invariant `I : A -> Sort0` and a postcondition `Q : R -> Sort0`, the law is:

`GoodNat N -> (Pi s mu. I s -> Q z) -> (Pi f. Good f -> Good (B f)) -> Good (M (loop body) N R k z)`

Its proof is one line: `gn (\m. Good (m _ B out)) hz (\j ih. hs _ ih)`. The base and step types match by conversion.
- **Instance:** `loop L { push 1; sub; br L }` times out (`= z`) for every fuel with `GoodNat`. The step discharges
  `Good (B f)` by applying `Good f` to the decremented stack.
- **At fuel 50,** the theorem with the canonical `GoodNat 50` agrees with `refl`.

Controls, all rejected:

| what | how |
|---|---|
| `eq a a = true` lemma | stated `= false` |
| forwarding law | claims the address is loaded back |
| forwarding law | `eq` premise replaced by `refl` |
| loop instance | same proof stated as "answers `k(x, mu)`" |
| concrete loads | `= k(7)` |

Check times (s), on a machine at 60% CPU from other jobs; Defender real-time protection off:

| n | eq refl | forwarding law | forwarding use | loop law | loop instance |
|---|---|---|---|---|---|
| 4 | 0.0009 | 0.020 | 0.004 | 0.013 | 0.004 |
| 16 | 0.003 | 0.022 | 0.004 | 0.013 | 0.003 |
| 32 | 0.010 | 0.025 | 0.013 | 0.015 | 0.005 |
| 64 | 0.049 | 0.083 | 0.021 | 0.020 | 0.008 |

Only the `eq` lemma grows with n; the rest stays near flat.

An invariant across an `if` needs a case split on the condition bit at Sort0, where `Q` lives. Shown in the next
paragraph.

**An invariant across an `if` (probe 2026-10-17, `docs/runs/2026-10-12/patches/if_invariant_probe.patch`; its pieces
are kept since: `good_lt`, the lowering and `lowering_and_lt_witnesses_check` in `crates/church-bv/src/encoding.rs`, `choose`
and `if_inv` in `crates/church-bv/src/wasm.rs`, next-but-one paragraph).**
Derivable, with no kernel change, and cheap. Three pieces, all checked:
- **A Sort0 split from the Sort1 witness.** `GoodBool0 a = Pi P:(Bool0 -> Sort0). P true -> P false -> P a` is a
  Sort1 type, so `GoodBool a` eliminates at the motive `\b. GoodBool0 b`: `lower_bit : Pi a. GoodBool a -> GoodBool0 a`
  is one application. A word lowers the same way, shaped as `lift_good`: `lower_bv : Pi x. GoodBv x -> GoodBv0 x`,
  where `GoodBv0`'s motive is `Bv_n -> Sort0` and its step takes `GoodBool0` witnesses (`GoodBv0 x` is a Sort2 type,
  so it is a legal motive for `GoodBv`).
- **The If invariant.** `Pi R:Sort0. Pi Q:R->Sort0. Pi w:Bv_1. GoodBv w -> Pi x y. Q x -> Q y -> Q (choose w x y)`,
  with `choose` as above (`Lift R`): lower `w`'s witness, eliminate it at `\w. Q (choose w x y)`, and split the bit at
  `\b. Q (choose (mk b) x y)`, which reduces to `Q x` and `Q y` at the leaves.
- **The compare's witness.** `good_lt : Pi a b. GoodBv a -> GoodBv b -> GoodBv_1 (lt_u a b)` is `good_sub`'s borrow
  chain keeping only the last borrow, through `good_vec` with its result width taken from the result bits (the patch
  generalises `good_vec` from n to m output bits; for n-bit results nothing changes).

Composed, `Pi a b. GoodBv a -> GoodBv b -> Pi R Q x y. Q x -> Q y -> Q (choose (lt_u a b) x y)` for symbolic `a`, `b`.
Check times, machine at 32% CPU from other jobs, Defender real-time protection off:

| n | `good_lt` | `lower_bv` | composed invariant |
|---|---|---|---|
| 1 | 0.08 ms | 0.02 ms | 0.11 ms |
| 4 | 0.14 ms | 0.03 ms | 0.14 ms |
| 16 | 0.39 ms | 0.07 ms | 0.24 ms |
| 32 | 0.67 ms | 0.13 ms | 0.37 ms |
| 64 | 1.86 ms | 0.30 ms | 1.14 ms |

(`if_inv` alone, at width 1, 0.13 ms.) Controls, all rejected:
- the false leaf given `Q x` (type mismatch at the leaf);
- the witnesses eliminated at Sort0 directly, without lowering ("inferred Type0, expected Type2"): the universe
  obstacle is real, and lowering is what removes it;
- the conclusion stated as `Q x`;
- `lower_bv` passing the unlowered `GoodBool` witnesses;
- the composed statement for `lt_u b a` at every width.

Concrete: `choose (lt_u 0 1) x y` is `x`, `choose (lt_u 1 0) x y` is `y` and not `x`, by conversion at n=4 and 64.

**Wasm programs as kernel data, kept (2026-10-17; `crates/church-bv/src/wasm.rs`, test `wasm_programs_as_kernel_data`).**
The instruction-list encoding, rebuilt a third time and now in the tree. A program is a Church-encoded instruction tree
typed by its start and end stacks, `Prog S T = Pi F:(Sort2 -> Sort2). F T -> push -> bin -> cmp -> dup -> if -> loop
-> store -> load -> F S`, each constructor taking the rest of the program, so `p1 ++ p2` puts `p2` at `p1`'s nil. Its
meaning `M p N R k z` reads `F A` as `A -> Mem -> R` (`R : Sort0`, stacks nested `Sigma` pairs,
`Mem = V -> (V -> R) -> R`, store as `upd a v mu = \b kk. eq a b R (kk v) (mu b kk)`); `if` is `choose` on its bit, and
`loop` unrolls its body `N` times (`N` a Sort2 numeral) before answering the timeout `z`. Terms are built through a
small named-binder builder (`Cx`, `At`, telescopes shared by statement and proof), not hand de Bruijn indices.
Checked, with nothing postulated:
- **append law** `M (p1 ++ p2) k = M p1 (M p2 k)` over abstract stacks and programs, by `refl`;
- **If law** `Spec(c, m) -> M (c S ++ if t e) .. s mu = choose m (M t .. s mu) (M e .. s mu)`, `Spec(c, m)` saying
  code `c` pushes `m` for every continuation, as `Spec` at the continuation `M (if t e)`;
- **the invariant over `M`**: `Spec(c, m) -> GoodBv m -> Q (M t ..) -> Q (M e ..) -> Q (M (c S ++ if t e) ..)`, one
  `J` transport of `if_inv` along the If law;
- **loop law**: fixpoint induction, `GoodNat N -> (I -> Q z) -> (Good f -> Good (B f)) -> Good (N (G A) timeout B)`
  with `Good f = Pi s mu. I s -> Q (f s mu)`, `GoodNat` the numeral's induction principle as a hypothesis;
- **an `if` inside a loop**: `loop { dup; push 1; lt_u; if {} {push 1; sub; br 0} }` (count down to 0) satisfies `Q`
  for every fuel with `GoodNat` and every start word with `GoodBv`, if the timeout and the exit continuation do. `I`
  carries `GoodBv` of the counter; `good_lt` feeds `if_inv`, `good_sub` re-establishes `I`;
- **concrete runs by `refl`**: the countdown from 3 exits at 0 with fuel 4 and times out with fuel 3; `push 3; push 5;
  store; push 3; load` answers 5 with memory `upd 3 5 mu`.

Controls, each with a well-formed statement and a rejected proof: `if_inv`'s three; the If law and the invariant with
the arms swapped; the countdown with `add` for `sub`; the runs with the wrong answer (1, or exiting at fuel 3).

Check times (ms), CPU 20% from other jobs, Defender real-time protection off:

| n | `if_inv` | append | If law | invariant over `M` | loop law | countdown invariant | run, fuel 4 |
|---|---|---|---|---|---|---|---|
| 4 | 0.13 | 0.22 | 0.39 | 0.86 | 0.06 | 0.85 | 0.52 |
| 16 | 0.05 | 0.19 | 0.39 | 0.78 | 0.07 | **44.9** | 1.13 |
| 32 | 0.06 | 0.27 | 0.57 | 0.97 | 0.09 | **> 600 s** (stopped) | - |

**The countdown invariant was exponential in n under `conv` without a pair memo (fixed: kernel change, kept,
2026-10-17).** The program's else arm reaches `conv` as an
unreduced `push_i .. s mu` redex, the proof's as the reduced `f (sub x 1, s) mu`: equal, not the same node. Both sit
under `lt_u`'s borrow chain applied to `choose`'s continuations, and that chain's case tree shares its tail
(`or ab cx` uses `cx` in both branches), so a walk that doesn't remember pairs visits 2^n leaves, comparing the two arms
at each. `conv` kept no pair memo (a per-scope one was A/B'd for speed and reverted, 2026-10-12 run log). Now it keeps
`EQUAL`, the pairs one `def_eq` call has shown equal, checked after the `same` test (first as a probe,
`docs/runs/2026-10-12/patches/conv_pair_memo_probe.patch`). Unequal pairs need no entry: the first ends the call. With it the countdown invariant takes 0.79 / 1.43 / 3.17 / 6.09 ms at
n = 4 / 16 / 32 / 64, the other checks move within noise, and the controls are still rejected at n=64. On the proof
corpus it is neutral: `runs time --pcs` (`proof_cost_split`, cmp3d, 24 alternating pairs, d36897f against d36897f plus
the patch) gives job CPU median 2.070 / 2.016 s and best 1.531 / 1.516 s, the memo winning 15 of 24 pairs (median pair
-0.03 s). The machine was contended (other load 31-85% per run, the quiet gate off; a gated attempt found no quiet minute
in 95 min), Defender real-time protection off. Kept: the test `countdown_invariant_is_not_exponential` (n=24, under
2 s) took 19.6 s without it and fails; `wasm_scaling` runs to n=64 again (countdown invariant 0.86 / 1.53 / 3.62 /
8.57 ms at n = 4 / 16 / 32 / 64).

