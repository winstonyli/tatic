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
`crates/church-bv/src/wnat.rs`; runs `2026-11-07-o1-wnat` and `-2`).** The "single fold is ill-typed" result above holds for
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

**One generator proves stream laws at all widths, and the `Sort3` limit was never there (spike, 2026-11-07; `crates/church-bv/src/wfold.rs`; runs `2026-11-07-q2-fold-5` and `2026-11-07-q2-fold-final-2`).** A stream law here is a pair of terms with no `shr1` or `mul`, and `lt` only at the root of both sides or neither. `encode` reads two terms through `Machine` and `moore_encoding`, as `tree_proof` does at one width, and `proof` builds the theorem with no per-law code: one goodness induction per carry, the per-side case lemmas, one induction on the phi agreement, then the output. The statement is `Pi x.. good x.. i. l i = r i` over `wnat.rs`'s own `add`, `shl` and a `sub` built from `carry`; a root `lt` is its borrow stream (its value at `i` compares the low `i` bits), and the width-`n` result is its value at `n`.

The expected limit came from putting goodness in the fold's state: `Sigma(c, GoodBool c)` sits in `Sort2`, and a tag splits only into `Sort1`. Nothing needs that state. A carry's goodness is its own induction with `P` bound by `ind`'s telescope, so what crosses the tag is `P c`, in `Sort1`, and the phi agreement is a `Sigma` of `Id`s, also in `Sort1`. `GoodMaybe` stays as it was. What the W index does contribute is the nesting: `add (add x y) z` is one level, because an adder's output is a stream of the same type. Whether the Church index could carry this proof is untested. It could not state nested `add`s at one level, so it would need a statement about one machine's tuple of carries (inference).

Results:
- `(x + y) + z = x + (y + z)`, the first all-width proof of `add` associativity, in 16 ms (single reads here and below, untimed runs).
- 17 more laws in 0.8-36 ms, including `(x+y)+(z+u) = (x+z)+(y+u)`, `sub(x, x) = 0`, `sub(x, y+z) = sub(sub(x, y), z)`, `(x^y) + shl(x&y) = x + y`, `shl(x+y) = shl x + shl y`, distributivity of `and`, and five `lt` pairs, two of them not constant (`x < y = ~y < ~x`).
- Sweep: terms of two operator levels on `x`, `y`, `0`, `-1` with `add`, `sub`, `and`, `or`, `xor`, `shl1`, and `lt` of any two one-level terms, each paired with the first different term of the same width-4 table (an `lt` only with an `lt`): 45677 pairs, 45621 with an encoding, every one of whose proofs the kernel accepted, in 1752 s, peak commit 5044 MB. The other 56 are all `lt` pairs that differ at width 1 (`0 < -1 + -1` holds at width 4, not at width 1), so they are not laws at every width; the test checks that each pair with no encoding differs at some width from 1 to 6. Rerun after the `lt`-as-borrow change and the root-`lt` proof by its output (run `2026-11-07-x1-full-sweep`, fd83d64, each pair in its own region over `WFOLD_THREADS=10` workers): the same 45621 proved and 56 without an encoding, in 405 s, peak commit 4502 MB. This pairs each term with one representative, not every two terms of a class.

Controls: the associativity statement is `def_eq` to one written by hand from `add`; its proof is rejected against `x + (y + y)`; flipping one table bit in the encoding is rejected; `x + y = x` and `x < y = y < x` have no encoding, and the proof of `x < y = ~y < ~x` is rejected against `x < y = y < x`. The streams, read at 5 closed operand pairs, give the 3-bit words of 8 terms by `def_eq`, and a root `lt` at every position `p` compares the low `p` bits. The associativity theorem, applied to constant streams with their goodness witnesses, gives bit 2 of `(7 + 7) + 0` and rejects the opposite bit, so its hypotheses hold of real streams.

The review of this work found a wrong law the kernel could not catch. `Machine::step` then read an `lt` below the root as `sub` (an `lt` now outputs its borrow, which a parent would misread as a word), so `add(lt(x, y), z) = add(sub(x, y), z)` got an encoding and an accepted proof: a true statement about subtractor streams, false of the terms. No earlier test or sweep had a nested `lt`. `Machine::parse` now builds no machine for one, so neither encoding nor `side` can read it, and `moore_encoding` returns `None` for a root `lt` against a word (both 2026-11-07). The rewriter's score-only screen in `join.rs` had used the same parse, so it had counted an equal pair with a nested `lt` as a whole-term proof that proving mode could not build. It now agrees with proving mode (`fallback_counts_no_nested_lt_pair`, which fails on the old parse). The gate across that change (`r1-score-screen-gate2`, c11d0ab against 89bcef6, salts 1-3) found the same rules in 9 of 9 loops, equal M and held-out M, an exact walk, and match within 1.0-3.0 ppm, so no sweep law had used such a count. A proof here checks a statement about the streams `side` builds, so what ties a law to its terms is that reading, tested only by the closed-stream control above.

Where a sweep's time goes (1-in-97 sample, 469 proofs, run `2026-11-07-v2-build-profile`; 21 s under samply, phase timers 0.19 s encoding, 21.2 s building, 3.6 s checking in an untimed read). Of busy samples, `Law::proof` is 83% and the kernel check 10%. In the build, `by_cases` is 46% (its case trees), lowering to kernel terms (`width::ex`, `comp`) 31% of the whole, of which interning in `mk` 23%; `wnat::ind` 23%, `table` 13%, `Law::closed` 11%. Allocation, cloning and drops of the named tree `T` take about a third of self time (`ptr::write` 13%, `mi_free` 7%, `clone` 5%, drops 5%, malloc 6%). A `T` is a tree with no sharing, so each repeated table, step and motive is built, copied and lowered again, where the kernel's interned `Expr` (what `tree_proof` builds on) shares them; the build cost tracks the unshared size.

A port spike on kernel terms (2026-11-07, patch `docs/superpowers/spikes/2026-11-07-x2-kernel-table-lemma.patch`, not merged). Each table becomes `table_app`'s memoized closed lambda applied to its `T` operands, and each side lemma becomes `lemma_n`: its statement is lowered once as a closed lambda, and each leaf is `refl` of the bit the machine and the encoding give there. The same sample, with the same 469 tried and 1 without an encoding, went from 178.0 G to 39.1 G retired instructions (4.55x; two runs per arm agree within 0.2%), and from 23.3 s to 4.3 s of wall time in an untimed read. The wfold tests pass, including the false table rejected. In its profile (`docs/runs/2026-11-07/x2-port-profile/named.txt`), the lemmas drop out of the list. What is left: `Law::proof` 59%, `wnat::ind` 35%, `good_carries` 24%, the kernel check 23%, and lowering 18%. The rest of the cost is the induction's terms, which were still in `T` until the w1 port.

The w1 port (2026-11-07, commits 6a84229 to 6ec1c43, spec `docs/superpowers/specs/2026-11-07-wfold-on-kernel-terms-design.md`) builds the whole proof as kernel terms: `wnat.rs` and `wfold.rs` build `Expr` through `Cx`, the fold's steps go through `StepProof` as `tree_proof`'s do, and `T` serves only the families. The baseline is the spike rebuilt on b52c265. Both arms run the same 1-in-97 sample, with 469 tried and 1 without an encoding each (runs `2026-11-07-w1-verdict-base` and `-port`). Counts are in batches of 4 on CPU 4 (`docs/runs/2026-11-07/w1-counts/counts.log`):
- A/A: (median - best)/best is 0.0015 for the base and 0.0004 for the port; max/best is 1.0023 and 1.0145, the port's first run.
- Medians: over three rotated batches per arm, 41.07-41.17 G for the base and 17.89-17.91 G for the port. That is 41.10 G against 17.89 G for the whole process, 2.30x.
- Build span: a one-pair run (stride 45677, the same pair on both arms) counts 5.91 G and 5.89 G, the enumeration of the 45677 pairs plus that one proof. Without it, the build span is 35.18 G against 12.01 G, 2.93x.
- Sizes: the associativity proof has 4218 distinct nodes (2.5 M as a tree). Its inferred type has 199 (15577), within 2x of the statement's 166 (11823).
- Full sweep (run `2026-11-07-w1-full-sweep`, the form of `2026-11-07-x1-full-sweep`): the same 45621 proved and 56 without an encoding, in 36 s and peak commit 1094 MB. The x1 row reads 405 s and 4502 MB, but it ran the `T` build without the spike, so that ratio spans both changes. Both are single untimed reads; total CPU was at 67% when this one started.

What this does not show. There is no bridge to `Bv_n`, so no hand-written family can go yet: `bitwise.rs`, `shift.rs` and `symmul.rs` each prove a `Bv_n` statement through theirs. The families' stream theorems are about Church-indexed streams, and nothing outside `uniform/` uses any of them. `shr1` and `mul` are outside, neither being a left-to-right machine, and so is `lt` below the root. That every stream law gets a proof is not itself proved: `moore_encoding` finds an encoding for any two equal machines, and the sweep samples the rest of the path. The w1 port removed the name tables that held the generator to 4 variables and 12 case bits; no law over more has been run.

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
are kept since, in `crates/tatic-wasm/src/` from 2026-11-08: `good_lt` in `encoding/good.rs`, the lowering and
`lowering_and_lt_witnesses_check` in `encoding/tests.rs`, `choose` in `wasm.rs` and `if_inv` in `wasm/laws.rs`,
next-but-one paragraph).**
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

**Wasm programs as kernel data, kept (2026-10-17; now `crates/tatic-wasm/src/wasm.rs`, test `wasm_programs_as_kernel_data` in `wasm/laws.rs`).**
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


### v0.7's first steps: the census and the emit spike (2026-11-08)

The questions: how much of the corpus could an emitted-code proof cover with church-bv's wasm machine
(then in church-bv; now `crates/tatic-wasm/src/wasm.rs#Ins`), and can the kernel check an `If (a < b)` program against its source at n = 64?

**Today's install gate proves the model, not the code.** `kernel_verify` (`crates/tatic/src/jit.rs#try_install`) accepts
`prove_pure_expr` (`crates/tatic/src/proof.rs#prove_pure_expr`) for a straight-line term: `refl(denote) : Id(Int, denote,
denote)` over a postulated `Int` with eight bare operators and no axioms. Both sides are the same expression; no
instruction list or WAT is consulted, and `verify()` (wasmtime against eval on samples) is the only check that touches
emitted code. There is no instruction list in tatic: `lower_wat` writes WAT text from the IR tree (`ir.rs#Node`).

**Census (38 terms: 23 in `samples::corpus`, 15 in `test_corpus.rs`).** Measured by running each term through the real
pipeline (`compile_specialised`, the three provers on the compiled term, `JitEngine::apply` at all arguments 3) and
bucketing the instruction kinds of the WAT it emits (patch `docs/superpowers/spikes/2026-11-08-b1-corpus-census.patch`,
run `2026-11-08-b1-census`), against the machine as it stands (Push, Bin, Cmp, Dup, If, Loop, Br, Store, Load; closed
`add`, `sub`, `lt_u`; no locals, no calls, no signed compare, `eq_bv` a `Bool0` rather than a one-bit word):

| class | WAT kinds | terms | needs |
|---|---|---|---|
| A | `local.get`, `i64.const`, add, sub | 5: inc `v0 + 1`, doubling, and three after specialisation: `\v0. v0 + 5`, `3 + 4`, `\v0. 3 + 4 + v0` | parameter reads (`Push i; Load` or a new instruction); `3 + 4` needs nothing |
| B | A plus compares, mul, rem, `if`, `local.set`, `br` | 6: `straight_line`, `5 * 10 + 3` (specialised), gcd, gcd with two base cases, and two loops that specialise to `rec v0 v1 v2 = if v1 <= 0 then v2 else v0 (v1 - 1) (v2 + v1)` | `lt_s`, `le_s`, `eq` as a one-bit word, `mul`, `rem_s`; the four loops also locals and fuelled loops |
| C | calls, `call_indirect`, memory, globals | 26, plus `open_redex_probe`, which does not compile | calls, closure records |

All but 8 of the 37 compiled terms install today; every A and B term installs. The prove_pure_expr fragment is exactly the
five with `pure`: inc, doubling, `straight_line`, `\v0. v0 + 5` and `\v0. 3 + 4 + v0` (the arity-0 constants are
proved by `prove_closure_expr`). So the one straight-line term with a branch or a multiply and a parameter is
`straight_line`; the others are an add chain or a constant. Mul appears in 7 terms, Mod only in gcd, Div in none.

**Spike: the continuation form proves by refl at n = 64; the value form does not.** Patch
`docs/superpowers/spikes/2026-11-08-j1-emit-spike.patch` (a test module in church-bv), runs `2026-11-08-j1-spike-head2`
(HEAD 461fa5f) and `2026-11-08-j1-spike-all` (base c37d273, within 1 ms of these at n = 64). Parameters live in memory: `local.get
$p_i` is `Push i; Load` over `upd 0 a (upd 1 b mu)`. `lt_s x y = lt_u (x ^ m) (y ^ m)` with `m` the sign bit, and `mul`
is `bits_circuit(n, mul_bits)`. The statement for `straight_line` (`\a b. if a < b then a * 2 else b + 1`) is
`run(code) S R k s mu = choose R (lt_s a b) (k (a*2, s) mu) (k (b+1, s) mu)`, closed by `refl`.

| n | inc | `a+a` arm | `a*2` arm | value form | doubling d = 16 |
|---|---|---|---|---|---|
| 8 | 0.4 | 0.9 | 0.7 | FAIL | - |
| 16 | 0.6 | 1.2 | 2.3 | FAIL | - |
| 64 | 1.6-1.7 | 4.9-5.5 | 12.8 | FAIL | 1.7 |

(ms, check only; building the statement adds 8-17 ms at n = 64.) Every control is rejected at n = 8, 16 and 64: arms
swapped, the else arm's add changed to sub, the constant 2 changed to 3, `lt_s` changed to `lt_u`. The value form
(`ite_w (lt_s a b) (a*2) (b+1)`) fails because a symbolic comparison bit is neutral: `ite_w` cannot reduce it, while the
program's `If` reads it through `choose` with the continuation copied into both arms, so the two sides never meet by
conversion. A gate states its claim in continuation form.

**What it proves: wiring, not operators.** Both sides use the same `lt_s` and `mul` terms, so the proof says the
instruction list computes the source's expression tree over these operator terms. That `lt_s` is signed less-than and
`mul` is 64-bit multiplication, and that both agree with eval's i64 semantics and wasm's i64 ops, needs separate
operator lemmas (or a trusted operator table). The design choices this left (where the code lives, how it meets
`proof.rs`'s `Int`, where the list comes from, operators) are decided in ROADMAP v0.7.

### v0.7's build: measurements and checks (2026-11-08)

The checks and measurements the v0.7 plan (`docs/superpowers/plans/2026-11-08-v07-straight-line-gate.md`) takes on
the way to the gate.

**The closure prover covers what `prove_pure_expr` accepted.** Before `prove_pure_expr` is deleted, terms outside the
fragment must still install through `prove_closure_expr`. A temporary probe in `kernel_verify` and in `ir_fuzz`'s
reference run printed, for every term `prove_pure_expr` accepted, whether `prove_closure_expr` accepted it too, over
the whole tatic suite (run `2026-11-08-v07-c1-closure-covers`): 932 lines, 170 distinct terms, all covered, no miss.
A temporary test also checked the three terms the plan relies on to install through the chain:
`\a b. 1 + (if a < b then a else b)`, `\a b. if (if a < b then a else b) < 1 then 1 else 0` and `\a b. a / b`, all
accepted. The probe was reverted.

**The operator table agrees with eval and wasmtime.** `crates/tatic/src/jit/op_table_tests.rs` checks each `Op` row
three ways: `\a b. a OP b` (or `if a OP b then 1 else 0` for a compare) through `eval::apply_term`, the same source
through the production lowering under wasmtime, and the row's kernel circuit by `def_eq`, all at n bits with the
arguments sign-extended to i64. `Op::LtU` has no source operator, so only its circuit is checked, against unsigned `<`.
Each check was shown to fail on its own: mapping `Lt` to `LtU` in `shape::op_of` broke eval against wasm at
`(MIN, 0)`, and giving `Op::LtS` the `lt_u` circuit broke `def_eq` there. The default test (n = 64) first used
`ir_fuzz.rs`'s 8 edges squared and took 4.0 s, 3.9 s of it in `mul`'s circuit; cut to `{MIN, -1, 0, 1, MAX}` it takes
1.6 s (`mul` 1.5 s), still over the plan's 1 s, and kept as the only always-on guard on the table (debug build, one test
thread of a parallel suite); the 8 edges run ignored since (`op_table_agrees_at_n64_on_all_edges`, 5.0-6.1 s after
the `karrow` fix, `mul` 4.9-6.0 s of it, so that fix did not touch `mul`'s circuit check). The ignored n = 8 test runs all 65,536 pairs per row and passed in 47 s, `mul` 26 s of it
(run `2026-11-08-v07-op-table-n8`).

**The gate's costs, and the rules they triggered.** `proof/gate.rs` proves the emitted body of a fragment term equal to
the source at n = 64 (`gate`); its tests accept the 5 Goal 1 terms and 4 more, and reject every Goal 2 mutation and a
`Raw` line. Spec section 8's measurements ran on the production statement builder and check (`measure_gate_costs`,
run `2026-11-08-v07-gate-measure_gate_costs`; tatic's test profile is optimized with debug info), build ms + check ms:

| term | build | check |
|---|---|---|
| `inc`, fuel 1 on the `loop` wrapper | 7.2 | 1.4 |
| `inc`, bare body, fuel 0 | 7.3 | 1.4 |
| `doubling(4)` (32 nodes) | 28 | 2.7 |
| `doubling(7)` (256 nodes) | 250 | 21 |
| `doubling(8)` (512 nodes) | 606 | 51 |
| `doubling(10)` (2048 nodes) | 2520 | 531 |
| `doubling(13)` (16,384 nodes, the JIT's tree cap) | 26,126 | 67,580 |
| `\a b. a * b` | 12.7 | 12.3 |
| `\a b. if a < b then a * b else a` | 16.3 | 17.3 |

- **Fuel 1:** the wrapper costs nothing measurable, so the gate proves `[Loop(body)]` as printed; no fallback and no
  trusted "a `loop` with no `br` is its body" fact.
- **Tree size:** the build doubles with the tree (linear) and the check grows faster (5.8x from d = 12 to 13), so the
  gate alone passes the JIT path's 0.4 s at 512 nodes, far below the 16,384-node cap. `in_fragment` takes trees of at
  most 256 nodes (`MAX_GATE_TREE`, `doubling(7)`; 1024 since the build fix below, 2048 since the shift memo below, 8192 since the build's constants below); a larger straight-line term
  installs through the existing chain.
- **`Mul`:** 25-34 ms with two parameters as operands, so `Mul` stays in the fragment unrestricted.
- **Stack:** building and proving `doubling(13)` on a 2 MB thread overflowed (run `2026-11-08-v07-gate-measure_stack_2mb`),
  so `Wasm::seq` and the gate's `cps` now run each step under `tatic_kernel::grow`; the same run then passed in 105 s
  (run `2026-11-08-v07-gate-measure_stack_2mb-grow`). It stays an ignored test: the bound keeps such trees from the
  gate, and 105 s is no default test.
- **After `grow`, and nested `Mul`:** the table above was measured before `grow` was added. Rerun with it (run
  `2026-11-08-v07-gate-costs-after-grow`, cpu 26%, one rep per tree): `doubling(7)` 305 + 19 ms, `doubling(8)` 591 +
  44 ms, `doubling(13)` 31,968 + 104,208 ms. The bound stands: 256 nodes is the largest power of two under the JIT path's
  0.4 s. Products of symbolic products cost no more to check than one: `(a*b)*(a*b)` 25 + 10 ms, `(a*b)*(b*a)` 29 + 10
  ms, and a chain `a * b * .. * b` of k products builds in 24 ms (k = 2) to 48 ms (k = 8) and checks in 10-13 ms
  throughout, so `Mul` needs no rule of its own.
- **The build was `karrow`:** a samply profile of the build at `doubling(7)` and `(8)` (run
  `2026-11-08-gate-build-profile`) put 61% of its samples under `Wasm::sty` -> `word` -> `bv_ty` -> `karrow`, all of
  it `arrow`'s codomain shift: `karrow(n)` nested n arrows, so each 64-bit word type cost about 2,000 node shifts, and
  `sty` makes one per stack slot per instruction. Rebuilding `Op::term(64)` per instruction (0.25 ms each) and building
  `prog` twice were the smaller part. `karrow` now writes its binders directly, as `bool0` does
  (`karrow_is_the_arrow_chain` pins it to the arrow chain). Rerun (run `2026-11-08-gate-costs-direct-karrow`, cpu 77%,
  one rep per tree): `doubling(7)` 17 + 26 ms, `doubling(8)` 34 + 53 ms, `doubling(9)` 66 + 184 ms, `doubling(10)`
  126 + 790 ms, `doubling(13)` 1,748 + 102,289 ms. The build is now linear and small; the check grows about 4x per
  doubling from d = 9 and is the whole cost above 512 nodes. By the same rule the bound is now 1024 nodes
  (`doubling(9)`, 0.25 s even at 77% load; `doubling(10)` takes 0.92 s); the table test accepts `doubling(9)` and
  `in_fragment_rejects_the_rest` refuses `doubling(10)`. The sweep barely gains: in a samply profile of a salt-1 sweep
  on the build before the fix (run `2026-11-08-karrow-sweep-profile`, 199,220 busy samples) `karrow` is 0.62%
  inclusive, since the sweep mines at small widths, where the n^2 / 2 shifts are few. That share caps the gain, so no
  sweep A/B was run.
- **Why the check grew 4x per doubling:** `shift_child` memoised only shared nodes, by the rule for a walk's memo (doc
  14, "Walk memos store only shared nodes"): a repeated walk stops at the parent's entry first. But shifts start from
  call roots with no entry, and the check reached the same unshared program suffixes from such roots at every step: at
  `doubling(9)`, 2.43M shift calls over 11,823 distinct (node, cutoff, amount), 97% of the left side's whnf work (run
  `2026-11-08-o5-check-growth`, a probe). `shifts` now keeps every node (`hc`'s module doc). The check's kernel work at
  `doubling(7)`, `(8)`, `(9)` fell from 216k, 715k, 2.60M to 59k, 106k, 201k, and `gate_check_work_is_linear_in_the_tree`
  fails above 2.6x per doubling (the old memo gave 3.3x and 3.6x; runs `2026-11-08-memo-check-work-a` and `-b`). Rerun (run `2026-11-08-memo-gate-costs`, cpu 44%, one
  rep per tree): `doubling(10)` 184 + 147 ms, `(11)` 402 + 309 ms, `(12)` 945 + 828 ms, `(13)` 2,265 + 2,495 ms, against
  102 s of check before; the build now grows 2.2-2.4x per doubling too (next bullet). By the same rule the bound is
  now 2048 nodes (`doubling(10)`, 0.33 s; `doubling(11)` takes 0.71 s). The church-bv gate is unchanged (run
  `2026-11-08-memo-gate3`, salts 1-3: M 447 and held-out M 5166 both arms, rules the same in 9 of 9 loops, peak process
  3,336 MB both). Its pin test (`streams::stream_sequences_are_pinned`, about 863 G instructions) passed on both arms
  and counts the same (run `2026-11-08-memo-count-rot2`, 2 runs per batch, batches a b b a b a a b on CPU 4, cpu 37%):
  the two flat batch pairs (max/best 1.0002 or less) differ by -0.001% and -0.010% in B's favour, and the first two pairs
  (max/best up to 1.004, the large-page wander of doc 14, "Why a retired-instruction count wanders") by +0.15% and
  +0.30% against it.
- **Why the build grew 2.2x per doubling:** the build rebuilt closed constants. Profiled at
  `doubling(7)` to `(13)` in release (`2026-11-08-build-growth-profile2`, samply), 80% of its samples sit in
  hash-consing: `seq_step` rebuilds `bv_ty(64)` for every slot of every instruction's stack type (49% inclusive), and
  `Op::term` the operator's circuit at every `Op` (15%). A stack slot's type costs `O(depth)` per instruction, the
  log factor. `statement` also builds the left side twice, once for the statement and once in `refl`. Memoising
  `bv_ty` and `Op::term` per interning generation (as `gates::constant` does for closed constants) and building `sty`
  with one shift of the base took the release build at `doubling(13)` from 837 ms to 64 ms, its kernel work from 738k
  to 148k, 1.98x per doubling. Test profile, one rep each (`2026-11-08-build-memo-gate-costs`, cpu 25%):
  `doubling(11)` 30 + 166 ms, `(12)` 42 + 317 ms, `(13)` 94 + 738 ms. The spike
  (`docs/superpowers/spikes/2026-11-08-build-memo.patch`) added two thread-locals, which church-bv's
  `hidden_state_is_classified` rejects; as landed, `gates::constant`'s one memo takes a key and `constant_n` builds a
  family of closed terms once per (builder, width), used by `bv_ty` and `Op::term` (`Source::op`'s local cache went), and
  `gate_build_work_is_linear_in_the_tree` fails above 2.05x per doubling (1.94x, 1.97x). Timed, before against after,
  A B A B, best of 3 per tree (runs `2026-11-08-gate-ab-a1-t18`, `-b1-t8`, `-a2-t8`, `-b2-t6`, cpu 12-24%, after 34
  refusals on a busy machine), build + check in ms: `doubling(12)` 491 + 285 and 477 + 290 before, 45 + 334 and
  41 + 306 after; `(13)` 1105 + 733 and 969 + 604 before, 96 + 788 and 85 + 656 after. The check is the same on both
  arms (its kernel work too, within 0.04%), so the faster check of the one-rep run was the 44% load of the run before it;
  after reads 5-15% higher at d = 12 and 13, inside the wall noise here. By the 0.4 s rule the bound is now 8192 nodes
  (`doubling(12)`, 0.35-0.38 s; `doubling(13)` takes 0.74-0.88 s), set by the check.
- **Where the check's time goes at the bound (profile):** `doubling(13)` in release took 80 ms to build and 641 ms to
  check (run `2026-11-09-check-profile`, samply, 759 busy samples, one run). The check is weak-head reduction of the
  machine: `whnf_in` 35% inclusive, of which `whnf_sigrec` / `beta_spine` 28% (stepping the stack records), and
  `instantiate_n` 31%, which is mostly the hash-consing it drives (`Spaces::node` 19%, `Spaces::build` 17%) and the
  `hc::uses` test that lets an instantiation skip a subterm (12%). No frame stands out on its own; the largest leaf is
  hashbrown's probe (`_mm_movemask_epi8` 5%, `probe_seq` 4%). Doubling the bound would need the check to be more than
  twice as fast, so it stays at 8192 until the machine's reduction changes. Half the gate's build was its proof's copy
  of the lhs (build work 37491 against 18792 without it at `doubling(11)`, a one-off probe). `encoding::law` now walks
  its telescope once, its body giving the proof and the statement together, so every law builds a subterm the two
  share once (the gate's lhs and frame, `wfold::proof`'s machine sides, the `refl` laws of `wasm/laws.rs`); the gate's
  build work at `doubling(11)` went from 37491 to 18774. The check is unchanged by it: the kernel interns both copies as
  one node and the checker memoises shared nodes.
- **Where the check's wall time goes past linear:** the check's wall time grew 2.1-2.3x per doubling, but its kernel
  work does not (run `2026-11-09-check-shapes`, two one-off probes at 02c10f1). Work per doubling of `doubling(d)` rises
  toward 2.0 from below, 1.68, 1.81, 1.89, 1.94, 1.97 for d = 7 to 11 (a fixed cost amortising), and a left-deep chain
  `t = add(t, x)` of the same tree size gives the same work within 1% at each d (776575 against 768735 at d = 11), so
  the stack depth of `doubling`'s machine program is not the cause either. What grows is the cost per unit of work:
  in release, best of 3, 112 ns at d = 6, 146-149 at d = 7-8, 185-205 at d = 9-11 and 235-239 at d = 12-13 (other
  sessions held about 49% of the CPU, so the levels are rough). The kernel's tables outgrowing the caches is the
  measured part of the cause; how much of the time it explains is open (next bullet). The check's footprint (region nodes, side arrays, table and memos, by capacity) doubles with d: 1.0 MB at d = 6,
  2.2 MB at 8, 16.5 MB at 11, 66 MB at 13 (525168 region nodes). Under cachegrind, with the last level simulated at
  the 7840U's L2 (1 MB) and L3 (16 MB), data references and L1 misses per doubling stay at 1.8-2.0, like the work, but
  last-level read misses do not (run `2026-11-09-cachegrind-doubling`, the check's misses taken as the difference
  of a build-only and a build-and-check run). At 1 MB they grow 2.2-2.7x per doubling, from 6449 at d = 6 to 3.93 M at
  d = 13. At 16 MB they are nearly zero through d = 9 (21-302), then 8060 at d = 10, 151127 at 11, 511902 at 12 and
  1.47 M at 13, so the jump starts where the footprint passes 16 MB. The two clear steps in time per unit of work
  (d = 6 to 7, d = 11 to 12) sit at those two crossings. cachegrind is close to deterministic here: the two runs of each
  d differed by a few ppm in data references and 0.06% in L1 misses. Raising the bound past 8192 therefore needs a
  smaller footprint per node, or a check that touches less of it, as well as less work. `docs/runs/2026-11-09/scripts/cg.sh`
  reruns the sweep on the ignored test `measure_cachegrind`; the footprint probe is in
  `docs/runs/2026-11-09/patches/y1-cache-probes.patch`.
  `gate_check_work_is_linear_in_the_tree` now holds the work ratio under 2.05, below the 2.1 a log factor gave.
- **What the check builds and where it misses (survey, 2026-11-09):** at `doubling(13)` the statement is 26520 region
  nodes and the check grows the region to 525168. Comparing the lhs with the rhs (`conv` under `def_eq_in`) builds
  498192 of the 498648 new nodes and does 40% of the work (1.21 M); typing the claim (`infer(expected)`) does 60%
  (1.83 M) and builds 455 (`docs/runs/2026-11-09/patches/a1-phase-probes.patch`). Memo hit rates in the check: whnf
  98% (157K entries, 7.62 M hits), shift 78%, spine 46%, inst 26% (164K entries); `bounds` holds 214K entries
  (`patches/z1-memo-probes.patch`). cachegrind by function (run `2026-11-09-cg-annotate-d13b`, debug-info build,
  `docs/runs/2026-11-09/scripts/cg_annotate.sh`): at a 16 MB last level, 34% of read misses are `memcpy` (`Vec`
  growth), about 14% table rehashes, 9% `whnf_step`, 5% `beta_spine`, 4% each `hc::uses`, `shift_get` and the node
  table's `find`; `whnf_get` is 0.3%, so the whnf memo stays in cache. At 1 MB the loose-variable and shift machinery
  leads: `hc::uses` 10%, `shift_unchecked` 7%, `Space::push` 6%, `shift_put` 5%, `shift_get` 4%. The misses explain
  only part of the time, an inference: the excess over d = 6's cost per unit of work is about 386 ms at d = 13 (about
  195 ms on a quieter machine: "Where the excess goes, profiled", below), and weighting the random misses by latency
  (about 0.7-1 M at 16 MB at ~80 ns, 3.9 M at 1 MB at ~10 ns) gives about 100-120 ms, while the `memcpy` misses stream
  and cost a few ms. cachegrind models no TLB and no prefetcher (the TLB was then tested, next bullet). Options, fewest
  concepts first: check the top
  telescope under fresh typed free parameters instead of `Var` binders, so the program is closed and the shifted
  copies of its suffix go (kernel, trusted base); one `u64` loose-variable mask per node in place of the `uses`
  slot, `bounds`, `lowest_loose` and `InferCache::lows`; `inst` as per-call scratch, deleting `arg_sets` and `Aid`;
  `whnf_in` returning non-redex tags without a probe and storing result -> result (a work cut, not a miss cut); one
  32-byte row per node in place of six arrays. Rejected: per-case encoding rewrites, lossy bounded memos, a custom
  table, narrower `loose`/`free`, a separate whnf slot array.
- **Testing the survey's options (2026-11-09):** four follow-ups, at 026f290 plus the change named.
  - *TLB.* mimalloc's large OS pages, on by default here, save only 4-7% of the check at d = 12-13 (best of 3, timed
    lease: d = 13 511 ms with them, 537 ms with `MIMALLOC_ALLOW_LARGE_OS_PAGES=0`; d = 12 246 against 265; runs
    `2026-11-09-lp1-*` and `2026-11-09-lp0-*`, `docs/runs/2026-11-09/scripts/lp.sh`), and the time still grows 2.03-2.07x
    from d = 12 to 13 either way. So large pages remove about 26 ms of the excess at d = 13, not the bulk of it; where
    the rest goes: "Where the excess goes, profiled", below.
  - *Closed parameters, the falsifier.* Opening the law's 7 binders onto postulated constants (public `whnf` of each
    `Pi` and `Lam` applied to a `Const`, then `Postulates::check`; `docs/runs/2026-11-09/patches/b2-opened-binder-spike.patch`,
    kernel untouched) cuts the memo tables at d = 13 by about two-thirds (shifts 162K to 50K entries, inst 164K to 34K,
    bounds 214K to 49K, arg_sets 90K to 25K) but the check builds more nodes, 680K against 499K, because the closed
    machine spine turns on `hnf` (49K entries, 77 before). Work falls 6.5% (3.04 M to 2.84 M; 6.3% at d = 11) and the
    untimed check 9%. The survey's estimate that nodes would fall to 40-70% was wrong: the option trades memo bytes for
    node bytes and is not worth a change to the trusted base on this evidence.
  - *A loose-variable mask.* A `u64` per node (56 bits of loose `Var`s and a byte for the lowest index lost to the cap)
    agreed with `hc::uses` on every query it answered exactly (141K of 160K random ones), the kernel and wasm suites and the gate at d = 6-13 (identical work),
    but answers only 24% of the gate's `uses` calls exactly: the rest ask nodes whose loose variables run past 56, under
    the 64-binder word telescopes, though only 1.6% of queries have d + m of 64 or more
    (`docs/runs/2026-11-09/patches/b3-mask-spike.patch`). One word cannot replace `bounds` and the slot; rejected.
  - *The whnf fast path,* adopted (`reduce.rs#whnf_in`): non-redex tags skip the memo and a reduced result is stored as
    its own whnf. The check's work falls 1.9% at d = 13 (3039350 to 2981514) and 2.7% at d = 6; the ratio per doubling
    is unchanged (1.992 from d = 12 to 13). Too small to time.
- **Where the excess goes, profiled (2026-11-09):** xperf traces (sampled stacks and faults, large pages on, untimed,
  other load 4-12%) of repeated checks at d = 6, 8, 11 and 13, all on one build with 4892e62's kernel (runs
  `2026-11-09-c1-xperf`, `2026-11-09-c1-xperf-small` and `2026-11-09-c1-xperf-few`;
  `docs/runs/2026-11-09/scripts/prof.sh`, `prof_report.sh`, `prof_agg.py`). Each d has two traces with different
  numbers of checks, and a check's cost is their difference over the difference in checks, so the process's one-off
  costs (start, build, its 256 MB stack, exit) cancel. `measure_cachegrind` now repeats the check `GATE_REPS` times and
  takes its settings as test filter arguments, since the elevated profiler drops the environment. A traced check runs
  about 7% slower than an untraced one (523 against about 488 ms at d = 13).
  - *Size.* A check costs 107 ns per unit of work at d = 6, 126 at 8, 150 at 11 and 171 at 13. The excess at d = 13
    over d = 6's rate is 195 ms of 523, not the 386 ms above, which came from timings taken while other sessions held
    about 49% of the CPU.
  - *Where.* Mostly in the functions that probe a table or memo: interning (`Spaces::mk`, `find`, `Space::push`,
    `hash`) 44 ms (23%), `inst_rec` with its memo and `args_id` 27 ms (14%), `hc::uses` and `lowest_loose` 26 ms
    (14%), the shift memo 20 ms (10%), `spine` 9 ms (4%); the checker's own closures 29 ms (15%); Windows' kernel
    18 ms (9%); mimalloc 7 ms (4%); 15 ms elsewhere. The kernel's part is noisy (8.0 ns per unit of work at d = 11,
    6.0 at 13) and its cause untested: soft page faults (`KiPageFault`) and working-set trimming (`MiTerminateWsle`,
    `MiActivePageClaimCandidate`) are both among its frames. From d = 11 to 13 the excess is 64 ms, led by interning
    (27%), the inst memo (24%) and the shift memo (19%); its top functions, `Space::push` (15%) and `shift_get` (14%),
    are also among the top 1 MB misses above.
  - *Against the misses.* cachegrind of a repeat check (`REPS=2` less `REPS=1`, run `2026-11-09-c1-cg-reps`,
    `scripts/cg.sh`) at d = 13: 3.37 M read misses at 1 MB and 0.81 M at 16 MB, against 3.89 M and 1.56 M for a first
    check, which also copies and rehashes as its arrays grow. At about 10 ns for an L2 miss that hits L3 and 100 ns
    for one that goes to memory, these come to about 107 ms, 55% of the 195 (inference: nominal latencies, no
    overlap); with the kernel's 18 ms, about 64%. The rest is not attributed; write misses (2.7 M at 16 MB per repeat
    check; attributed after the per-call memo, below: "After the per-call memo, the inst gate and the write misses"), TLB walks (large pages are worth about 26 ms, above) and the latency guesses are the candidates. The 100 ns
    weight may be high: by it, the first check's extra random (rehash) misses at 16 MB, about 0.22 M, would cost it
    about 20 ms more than a repeat, and the next sub-bullet measured 4.7 ± 5.0. Separating these needs per-function hardware miss counts,
    which the Samply task does not record.
  - *Growth costs nothing measurable.* A first check (arrays and tables growing, with the `memcpy` and rehash misses)
    and a repeat check (`scoped` keeps capacity) take about the same time: medians 490.8 and 487.2 ms at d = 13, 112.2
    and 114.2 at d = 11, from 10 processes of 3 checks (untimed, other load 17%); first minus the mean of the repeats,
    paired, +4.7 ± 5.0 ms (standard error) at d = 13 and -0.8 ± 2.0 at d = 11 (run `2026-11-09-c2-reps-b`,
    `scripts/reps.sh` with `N=10`). So presizing the region would gain at most about 3% at d = 13 (95% interval
    -6.6 to +16 ms), too little to justify it without a timed A/B: `PARKED.md`, item (i).
- **The survey's last two options, spiked (2026-11-09):** at 14fb70a, checked by cachegrind (the check's misses, c = 1
  less c = 0) and work, each spike reviewed and one cachegrind config reproduced by a second agent.
  - *One 32-byte row per node,* rejected. All six per-node fields are 38 bytes, so the row that fits holds the tag,
    `parents` and `height` in the node's padding, five child slots, `loose` and `free`, with `uses` kept apart (variant
    B swaps `uses` in and `free` out). Work is identical at d = 6-13, but read misses do not fall: +0.5% at 1 MB and
    0.0% at 16 MB at d = 13, +3.2% at 16 MB at d = 11; write misses fall 1.3-2.2% (runs `2026-11-09-d1-row-cg`,
    `2026-11-09-d1-row-b-cg`; `docs/runs/2026-11-09/patches/d1-row-spike.patch`, `d1-row-b-spike.patch`). So the
    misses that grow are not the per-node arrays read side by side but the tables and memos.
  - *`inst` as per-call scratch* (`patches/d1-inst-scratch-spike.patch`): the memo is keyed (node, depth) and emptied at
    each top-level `instantiate_n`, since the argument list is fixed within a call and nothing reachable from `inst_rec`
    calls `instantiate_n` again; `arg_sets`, `args_id`, `Aid` and `LIST_BIT` go (+24 / -66 lines). Work rises 2.4% at
    d = 11-13 (3055582 to 3129184 at 13): the old memo's cross-call hits were few, and the map now holds at most 64
    entries between calls. The check's read misses fall 11.7% at 1 MB and 14.5% at 16 MB at d = 13 (11.6% and 19.5% at
    d = 11), write misses 9.7-12.5% (run `2026-11-09-2026-11-09-d1-inst-cg`, reproduced by
    `2026-11-09-2026-11-09-d1-inst-verify`). Time, untimed and contended (other load 33%, a game; the timed lease
    refused at 38%, run `2026-11-09-d1-ab-timed`), 12 paired rounds in ABBA order (`docs/runs/2026-11-09/scripts/ab.sh`,
    run `2026-11-09-d1-ab-untimed`): the spike was faster in 10 of 12 rounds at each d, best of 12 573 against 641 ms at
    d = 13 (-11%) and 124 against 143 at d = 11 (-13%); paired means -77 ± 29 and -32 ± 10 ms. Timed on a quiet machine (total
    CPU 3-5%, `run.ps1 -Timed`), 10 paired rounds each, two runs: medians 485.6 to 442.4 and 460.9 to 421.6 ms at
    d = 13 (paired -42.0 ± 4.8 and -41.5 ± 6.1), 107.8 to 101.4 and 105.8 to 98.5 at d = 11 (-6.2 ± 1.4 and
    -5.8 ± 2.0) (runs `2026-11-09-d1-ab-timed2`, `2026-11-09-d1-ab-timed2-2`). Adopted in f0e6b09, with a debug
    assertion that `instantiate_n` never re-enters.
- **After the per-call memo, the inst gate and the write misses (2026-11-09):** at f0e6b09, by cachegrind's instruction
  count (`I refs`) and misses for the check, one debug-info build with a knob choosing the gate
  (`patches/f2-inst-gate-spike.patch`, `scripts/f2_cg.sh`; runs `2026-11-09-f2-gate-cg2`, `2026-11-09-f2-gate-s0`).
  - *Which nodes get an `inst` entry.* The shipped gate (shared and height > 2) against the same gate with height > 0,
    1 or 3: work equal to within 3 units of 3129184 at d = 13, instructions within 0.09% (5341.0 M; 5345.5 M at
    height > 0), misses equal to within 0.01%. With no height cutoff, `Var` leaves get entries too: work falls 1.6%
    (to 3079830) but instructions rise 1.1% (5398.8 M). Without the shared test (any node with height > 2)
    instructions rise 4.7% (5590.7 M) and D1 misses 2.5%, for 0.3% fewer last-level read misses at 16 MB. The same holds
    at d = 11. So under the per-call memo the shared test still pays, and the height cutoff only has to keep out
    `Var` leaves: shared nodes of height 1-3 almost never reach the memo with a used argument. The old cutoff was
    chosen on church-bv's `proof_cost_split`, and there it still pays: retired instructions (ICOUNT.md, large pages
    compiled off, 3 rotated batches of 4 on CPU 4; `scripts/g1_pcs.sh`, run `2026-11-09-g1-pcs-counts2`) with height
    > 0 against height > 2 were higher in every batch pair, by 0.72%, 0.62% and 0.23% of the median (about 39.85 G),
    and 0.18% best against best, while each arm's batches wandered up to 0.24% among themselves. So the height field
    stays: dropping it costs 0.2-0.7% of a proof workload's instructions, and 0.09% on the gate too.
  - *Where a repeat check's write misses go.* `REPS=2` less `REPS=1` at d = 13, 16 MB: 2.39 M last-level write misses,
    attributed per instruction (callgrind with the same caches, totals within 30 of cachegrind's; two reviewers
    reran the numbers). Machine stack frames of the deep recursions 1.22 M (51%: the shift walk 0.34 M, `Spaces::mk`
    0.17 M, the wasm lowering's `seq_step` 0.13 M, `lowest_loose` 0.12 M, `hc::uses` 0.11 M, `inst_rec` and `infer`
    0.13 M); the interning table's bucket writes 0.36 M (15%; 68% of its 525168 inserts miss); the per-node arrays
    appended by `Space::push` 0.31 M (13%, one miss per 64 bytes of their 38 per node, to within 7); the memos' bucket
    writes 0.31 M (13%: `bounds` 0.14 M, `shifts` 0.10 M, `spine` 0.05 M, `whnf`/`nf`/`hnf` 0.02 M, `inst` about 0.1 k);
    mimalloc 0.15 M (6%). So the interning table is not most of them. About 69% are address-sequential (stack,
    appends, fresh allocator pages), which a hardware prefetcher may hide and cachegrind does not model; the random 28%
    are all hash-table bucket writes. Stack lines are partly first touches of the check's fresh 64 MB stack segment
    (`stack.rs`), whose cost on hardware is page faults, not misses (*The check's stack segment*, below). `hc::uses`'
    per-node slot store does not miss (the slot was just read).
  - *Which memo entries are read* (counters per memo and per entry, `patches/h1-memo-counters-spike.patch`, run
    `2026-11-09-h1-memo-parents-skips`; rep 2 of `GATE_REPS=2` counted directly, equal line for line to rep 1 since
    the memos are cleared at each region close). At d = 13 (d = 11 about a quarter, same rates): `inst` 221 k gets,
    14.8% hits; `shifts` 777 k, 79%; `whnf` 98.8 k gets, 21 hits, for 197 k inserts; `hnf` 8.5 k, 99%; `nf` none;
    `spine` 107 k, 46%; `bounds` 233 k, 3.5%. `hc::uses`' per-node slot answers 88.6% of what reaches it, and the rest
    goes to `bounds`, which inserts 214 k entries of which 31 are ever read (one shared node takes 8191 of the 8233
    reads), and no answered hit came from an `m` other than the storing call's. Skipping `bounds` inserts for
    unshared nodes (run, not simulated) leaves 359 inserts for 127 more walks (+0.01% of `uses` calls) and unchanged
    work (3129184). `spine` is the other way round: its unshared entries are read about once each (74% of them, by
    the next level of a stuck spine), while 26 of its 24.7 k shared entries take half of all its hits; skipping
    either class costs 8.6-15% more spine calls. Write-miss savings are inferred from insert counts, not measured.
  - *The check's stack segment* (`patches/h2-stack-probe-spike.patch`; runs `2026-11-09-h2-cg`, `-h2-winrun`,
    `-h2-wintime`). stacker makes a new segment per `grow` call (`CreateFiber`/`DeleteFiber` on Windows, `mmap` on
    Linux), so each large check faults its stack in afresh. Depth at d = 13: 61.7 MB on Windows (5.4 MB under the
    64 MiB segment), 46.1 MB on Linux; at d = 11 15.4 MB and 11.5 MB. Native page faults per check: 15107 at d = 13 and
    3804 at d = 11, about the pages touched; 0 with one segment reused across checks (from the second check; the
    first faulted 22% fewer pages than the depth, unexplained). The reuse arm was faster by 42-52 ms of about 570 ms
    at d = 13 (8-9%; untimed, at 29% machine load, and it also moves `statement()` onto the segment). Under cachegrind
    the segment sits at the same simulated addresses every check, so first touches cannot be told from re-touches;
    the depth bounds them at 0.72 M lines, at most 59% of the 1.22 M stack write misses. Since the segment is 3-4 times
    the 16 MB last level, reuse would not keep its lines cached; only smaller frames cut those misses.
    Shipped (cbcc4c1) as no segment at all where the thread has the room: `check_in` runs a large check in place when
    `stack::has_check_room()` holds, and church-bv's entry thread has a 256 MB stack (`CHECK_STACK`); a thread with
    less room takes the segment as before. church-bv's worker task threads and lanes were on default stacks and still
    took it; since 2026-11-09 they have the check stack too (their tests assert the room). A salt-1 sweep's commit,
    ae6f369's `entry.rs` and `driver.rs` against 6f1cb06, two sweeps each (`scripts/stack_commit.sh`, run
    `2026-11-09-q1-stack-commit`, 48-57% other load): the job's peak falls from 4537 and 4538 MB to 4490 and 4502 MB
    (-36 to -47 MB, about 1%), and the largest process's peak is 3336 MB in all four, so the segments were not at its
    peak. The 150 MB of the 2026-10-23 worker is not reproduced: that sweep (`cold:cmp3d`, 446-490 MB) no longer
    exists, and today's processes are seven times larger. Job CPU 168-171 s against 175-177 s, under that load no
    verdict; faults not remeasured. Page faults per
    repeat check, f159775 against cbcc4c1 (`scripts/faults.ps1`, run `2026-11-09-m1-faults`; the process's count at
    `GATE_REPS=3` less `GATE_REPS=1`, halved; 3 runs each, equal to within 6 faults): 15104 to 0 at d = 13 and 3802 to
    -2 at d = 11; the first check also faults less (20398 to 17054 and 6589 to 5730 for the whole process). Timed
    (run `2026-11-09-q2-m1-timed-1`, `scripts/ab.sh` under the CPU lease, total load 14%, n = 12 pairs): the repeat
    check at d = 13 is 29.4 +- 5.7 ms faster (438 to 410 ms median, 6.7%); the first check at d = 13 (-1.7 +- 7.2 ms
    of 432) and both checks at d = 11 (repeat +0.3 +- 8.9 ms of 107, first -12.5 +- 24.2) show no difference. An
    earlier untimed pair at 70% load could not see it (run `2026-11-09-m1-ab-untimed`: d = 13 rep 3 B - A
    -26.8 +- 22.9 ms of about 760; n = 20).
  - *One-probe interning* (`patches/h3-one-probe-intern-spike.patch`; runs `2026-11-09-h3-base`,
    `-h3-onepass-destructure`). `Space::build`'s region path with one `HashTable::entry` instead of `find` and
    `insert_unique`: instructions -0.44% at d = 13 (5279.96 M to 5256.51 M) and -0.47% at d = 11, -1.4% for building
    the statement alone; last-level and D1 misses unchanged (the second probe re-reads a group the first just loaded,
    an inference). Holding the vacant slot across the appends needs the region's fields borrowed one by one, so the
    spike copies `push`'s body into the region path; swapping the table out instead (`mem::swap`) cost +2.9%.
    Shipped as `Space { cols: Cols, table }` (`spaces.rs`): one `Cols::push` for every column, `Space::push` adding the
    table entry, and the region path holding the vacant entry across `Cols::push`, with no copied body. Cachegrind
    (runs `2026-11-09-wf1-j1-cg-2`, `-wf1-j1-cg-irefs`): d = 13 5261.82 M instructions (-0.34%), d = 11 1327.56 M
    (-0.36%); last-level misses unchanged (d = 13 16 MB 4,724,413 against 4,724,334).
  - *One bounds entry in the node's row* (runs `2026-11-09-wf1-i1-cg`, `-wf1-i1-cg-reps2`, `-wf1-i1-pcs-counts`).
    `Memos.bounds` and the per-node `(d, m, answer)` slot became one per-node slot of bounds `(lo, hi)` on the lowest
    loose variable from the last depth asked (`Spaces::bounds_slot`, one `u64`: `d` 15 bits, `lo` and `hi` 24 bits each,
    loosened by the caps only), so the walk's answer is stored once per node and read by any `m` outside the narrowed
    bounds. Cachegrind with the one-probe change in both arms: d = 13 5225.58 M instructions (-0.69% from 5261.82 M),
    d = 11 1318.48 M (-0.68% from 1327.56 M), d = 13 without the check unchanged (460.97 M; the -2.3% from 471.86 M is
    the one-probe change's); last-level data misses, all this change's, at d = 13 4,524 k at 16 MB (-4.2%; writes
    3,189 k against 3,383 k) and 8,753 k at 1 MB (-5.4%); d = 11 16 MB 821 k (-3.3%); `work` unchanged (3129184 at
    d = 13). Repeat check (`REPS=2` less `REPS=1`, d = 13, 16 MB): 2.25 M write misses against 2.39-2.44 M.
    Retired instructions of church-bv's `proof-cost-split`, both changes together (large pages off, CPU 4, 3 rotated
    batches of 4; paired batch medians, 9f65018 against both): 40.025 G to 39.496 G, 39.896 G to 39.469 G, 39.892 G to
    39.475 G (-1.32%, -1.07%, -1.05%; within-batch (median - best) / best 0.0001-0.0013); not split between the two.
    A timed pair of the gate check (`scripts/ab.sh`, run `2026-11-09-n3-ab-timed2`, 9f65018 against f159775, 10 paired
    rounds) cannot see a saving this size: d = 11 B - A +1.9 +- 3.6 ms of 107, d = 13 -20.7 +- 26.8 ms of 517. The
    count verdict stands as "less work", with no time claim.
  - *Whether the whnf memo pays* (at 9f65018; `patches/l1-whnf-counters-spike.patch`, run
    `2026-11-09-l1-whnf-counters2`; `patches/l1-whnf-memo-arms-spike.patch`, runs `2026-11-09-l1-ir`, `-l1-cg`,
    `-l1-pcs-counts`, `-l1-pcs-a1`, `-l1-tests`, `-l1-tests2`). The gate's check reads it 21 times for 197 k inserts,
    but `proof-cost-split` hits on 51% of 1.63 M gets (44% return a reduced term), the kernel's tests on 23% (nearly
    all stuck terms) and tatic-wasm's on 45%. Arms: no memo; the get and the `e -> r` put only (the `r -> r` put and
    its test-only whnf assert dropped). Without the memo the gate check retires 1.46% fewer instructions (d = 11 and
    13; last-level misses -2.3% to -3.2%, `work` +109 of 3.1 M), but `proof-cost-split` retires 14.4% more (45.62 G
    against 39.90 G, whole process, 3 rotated batches of 4) and 3 kernel tests fail, among them
    `nf_and_def_eq_are_linear_on_a_stuck_spine` (still running at n = 16000 after 20 s), so it stays. Dropping only the
    `r -> r` put: -0.78% (d = 13) and -0.77% (d = 11) on the gate check, -0.47% on `proof-cost-split` (39.71 G), all
    tests green, outputs identical; untimed, and it would leave `whnf_in`'s doc and `whnf_of_a_whnf_does_no_work`'s
    stated purpose (a reduced result answers without a `whnf_step`) out of date. Counted at 89% load in batch 1.
    Shipped (4ff9a86): `whnf_in` stores `e -> r` only, with the doc and the test's purpose rewritten (the first ask of
    a reducible-tagged result is one `whnf_step` that stores its own entry). The dropped put was already redundant for
    a beta result, since beta ends in `whnf_in` of the contractum, which stores it; it mattered only for results of J,
    WRec and SigRec steps and for an application whose head reduced to something stuck. Not timed (0.8% is under the
    timed pair's noise, above).
- **Against the old proof:** `prove_pure_expr`'s `refl` over the model of `straight_line` took 3.37 µs [3.20, 3.77]
  (criterion `straight_line_refl_proof`, untimed on a contended machine because the timed lease refused it at 42% load;
  run `2026-11-08-v07-straight-line-refl-baseline-untimed`), against the gate's 12-34 ms for a term of that size. The
  bench row is deleted with the prover.

**Fragment terms install on the gate's verdict alone.** `jit.rs#prove_install` sends a term in the fragment to `gate`
and nothing else, and every other term to `kernel_verify`, which no longer tries `prove_pure_expr` (deleted, with its
`setup`, `finish` and `LitScope::Arith`). A body with its `If` arms swapped is refused although the closure prover would
accept the term (`jit/tests.rs#the_gates_verdict_is_final_for_fragment_terms`); all five Goal 1 terms install, and an
operand `If`, outside the fragment, still installs through the chain. The workspace suite passed with 795 tests listed,
782 before the plan plus 21 added and 8 removed (run `2026-11-08-v07-workspace`).

### The sum loop proved against a source recursion: a spike (2026-11-10)

The question: before a v0.8 spec puts loops through the gate, can the kernel prove an emitted `loop`/`br` list equal
to a source-side recursion, and how should that recursion be stated? Target: the loop in
`tests/golden/partial_application_loop_specialised.wat` (p0 = x, p1 = acc, temporaries t0 and t1 at addresses 2 and 3),
written as `Ins` by hand. Throwaway; patch at `docs/superpowers/spikes/2026-11-10-sum-loop-spike.patch`, reverted.

**It proves, and it is cheap.** The statement is a fuel-matched simulation, for every fuel `N` with `GoodNat N`, every
answer type `R`, exit continuation `k0`, timeout answer `z`, start `x`, `acc` and memory `mu0`:
`M sum N R (\st mu. k0 st) z s (upd 1 acc (upd 0 x mu0)) = N (V -> V -> R) (\x acc. z) Bsrc x acc`, with
`Bsrc = \g x acc. choose (le_s x 0) (k0 (acc, s)) (g (x - 1) (acc + x))`. The source is the same step unrolled by the
same fuel, in the answer type. The proof is `GoodNat`'s induction on fuel: the motive quantifies over `x`, `acc` and the
memory under the frame (it grows by the two temporaries' stores each turn); the base is `refl z`; the step is one J
that pushes the hypothesis through the shared `choose`. `conv` did the rest: it reduced the loop body's loads through
the `upd` chain at literal addresses with no lemma. Run `2026-11-10-sum-loop-spike` (untimed, one run, 10% load):

| check | n = 4 | n = 24 | n = 64 |
|---|---|---|---|
| simulation (proved) | 2.3 ms | 3.3 ms | 6.9 ms |
| no-temps program against its own source (proved) | 1.2 ms | 2.1 ms | 5.8 ms |
| `sub` for `add` (rejected) | 1.0 ms | 2.0 ms | 3.8 ms |
| no-temps program against the sum's source (rejected) | 0.6 ms | 1.0 ms | 4.5 ms |
| run by `refl`: 3 from 0, fuel 4, answers `k0 (6, s)` | 1.9 ms | 3.5 ms | 10.4 ms |
| run by `refl`: fuel 3 times out | 0.4 ms | 0.6 ms | 2.3 ms |

The runs answering 5, or exiting at fuel 3, are rejected too. The no-temps program assigns `x` before reading it for
`acc`, so it computes `acc + (x - 1)`. Against the sum's source it is rejected; against that sequential source it is
proved, so the rejection is semantic, not an artefact of the proof's shape.

What it settles for a "loops through the gate" milestone (a v0.8 candidate; ROADMAP picks none yet):

- **How to state the source recursion:** as the source step unrolled by the machine's own fuel, in the answer type.
  Termination, `Ev` and value facts then belong to the source side only, and J transfers them. No relational
  big-step form was needed. The `Ev`-relational form was weighed as the fallback and not run.
- **The existing `loop_law` is not enough** (inference from its statement, not run): its invariant ranges over the
  stack only and `Good f` quantifies over every memory, so the body's first `Load` is stuck. A general loop law must
  take an invariant over (stack, memory), as this proof's motive does.
- **Continuations must ignore the frame.** With a general `k : G T` the two sides differ in the junk left in memory
  (the frame and temporaries), so an `Id` cannot hold. The spike restricts to `\st mu. k0 st`. A function's return
  ignores its locals, so this fits; the other way is a relational statement.
- **One J per `br` site**, through the `choose` that guards it. gcd and the two-`br` loops would need one each.
- **`local.set` has no `Ins`.** The lowering emits it as `Ins::Raw` (`crates/tatic/src/jit/lower_wat.rs`, the
  `local.set $t{i}` and `$p{i}` lines), and the machine's `Store` takes the address under the value, so the spike
  wrote `push i; <value>; store`. v1 needs a `LocalSet(i)` instruction, or a lowering that pushes the address first.

### Calls by index proved against a source recursion: a spike (2026-11-10)

The question: does a call fit the machine's universe levels, and can a non-tail recursion be proved against its
source? It was the open risk of a v0.8 with calls (`docs/decisions/2026-11-10-v08-shape-and-any-backend.md`, option
z3). Throwaway; patch at `docs/superpowers/spikes/2026-11-10-call-ctor-spike.patch`, reverted.

**A constructor that takes a program does not fit** (reasoning from the sort rules; not run). `Prog S T` quantifies
over `F : Sort2 -> Sort2`, so it lives at Sort3. A constructor with a `Prog` argument makes a new type `Prog'` that can
call `Prog` programs but not `Prog'` ones, since the Church encoding has no recursive type. Each layer adds one call
depth, so this form cannot express recursion.

**Calls by index into an environment fixpoint do fit, and they prove.** The callee's meaning is
`H = V -> Heap -> (V -> Heap -> R) -> R` (argument, heap, return continuation), at Sort2 like the existing `G A`. The
module's meaning is `N H (\x h k. z) B`, the same fuel fixpoint the loop uses. A `call` therefore needs no program
argument, so its constructor type would sit at the level of `bin` (inference; the spike built meanings by hand, below; the next
section builds it, with load's type).
The bodies are written in direct style. Locals are bound variables of the meaning, with no frame in the heap, so the sum
spike's "continuations must ignore the frame" restriction does not arise here. A machine built from `Ins` keeps its
locals in a frame. Whether per-activation frames, dropped at return, remove the restriction there too is untested. The
heap is passed through and never read or written, so only pure callees were covered.

The statement is relational in the continuations: for every fuel `N` with `GoodNat N`, every `R`, `z`, `x`, heap `h`,
machine continuation `km` and source continuation `ks`, `(Pi a h. km a h = ks a) -> M_N x h km = S_N x ks`, with
`M_N = N H (\x h k. z) Bm` and `S_N = N Hs (\x k. z) Bs`. The source is the same body with no heap. The types already force a relation, because
`km` takes a heap and `ks` does not. Fib also needs it to be a hypothesis rather than an equality the kernel computes
(reasoning; not tried another way). After the first call, the machine's continuation runs the second call on the machine
and the source's runs it on the source. The two are equal only by the induction hypothesis.

The proof is one fuel induction. In the step, the `then` branch is `rel` at the answer. The `else` branch is the
hypothesis at the call, with continuations and relation built from the outer ones. For fib, the outer call's relation
is the hypothesis at the inner call. Two J's push both equalities through the shared `choose`. Run
`2026-11-10-call-spike-2` (untimed, one run, 36% load):

| check | n = 4 | n = 24 | n = 64 |
|---|---|---|---|
| factorial law (proved) | 0.6 ms | 3.3 ms | 10.4 ms |
| fib law (proved) | 0.7 ms | 1.1 ms | 3.8 ms |
| factorial, machine base 0 (rejected) | 0.2 ms | 1.5 ms | 10.0 ms |
| fib, machine `sub` for `add` in the sum (rejected) | 0.4 ms | 0.7 ms | 2.2 ms |
| run by `refl`: fact 3, fuel 3, answers `k0 6` | 0.9 ms | 15.4 ms | 161 ms |
| run by `refl`: fact 3, fuel 2, times out | 0.2 ms | 1.8 ms | 9.1 ms |
| run by `refl`: fib 5, fuel 5, answers `k0 5` | 1.9 ms | 16.2 ms | 48.9 ms |
| run by `refl`: fib 5, fuel 4, times out | 0.2 ms | 0.4 ms | 1.9 ms |

The run answering 4 for fib 5 is rejected too. The two controls each change one value at a leaf (a base case, an
operator), and their proof terms come from the same builder as the proved laws. They do not test call structure: a
wrong argument, a dropped or reordered call, or a wrong continuation. The first attempt (`2026-11-10-call-spike`) failed on a de Bruijn bug in
the spike's own term building: a type built outside a binder was reused under it. It was not a kernel result.

What it settles for a calls milestone:

- **The universe risk is gone at the meaning level** for calls by index. The environment and the module's fixpoint
  check at Sort2. Whether `call`'s constructor slot fits the program type is untested here (see the limit below; the
  next section tests it), and the argument against a constructor that takes a program is reasoning only.
- **Still open, beyond size:** callees that read or write the heap, where the relation must link machine heap to source
  state (7 of the 26 class C terms keep closure records in memory; the next section tests a fixed cell only); the
  table; and the calling convention for closures.
- **The law is a simulation with a continuation relation**, the sum loop's statement generalised. It needs one
  hypothesis application per call site and one J per branch. The spike wrote each proof by hand for its function. A
  general law needs the per-call-site continuations derived from the instruction list, which was not tried.
- **Limit:** the machine meanings were written by hand at the meaning level. They were not derived from `Ins` through
  `prog` and `ctors`, so the constructor type of `call` and its `seq_step` row are untested. (The next section tests
  both.)

### `call` as an instruction, and a callee that touches the heap: a spike (2026-11-10)

The questions, left open by the section above: does `call` fit as a constructor of the program type, built through
`prog`; and can the relation link the machine's heap to the source's state when a callee writes memory and its caller
reads it after the call? Throwaway; patch at `docs/superpowers/spikes/2026-11-10-call-ins-spike.patch`, reverted.

**The machine change.** `Ins::Call` is a ninth constructor (index 8, after load at 7) with load's type,
`Pi A. F (V, A) -> F (V, A)`: it pops the argument and pushes the answer. Its meaning splits the stack and runs
`env x mu (\y mu'. rest (y, s) mu')`, with `env : H = V -> Mem -> (V -> Mem -> R) -> R` a new parameter of the
interpreter (`meaning_env`). Without an environment it answers the timeout. `Prog` keeps its level (Sort3). The change
touched `Ins`, `shape`, the constructor count, `seq_step`, `interp` and the printer (only its never-emitted panic list:
there is no `call` lowering to WAT); `ctor_ty` needed no new arm, since `call` falls into load's. With nine
constructors, the 31 existing tatic-wasm tests pass, plus the spike's own (run `2026-11-10-call-ins-regress-wasm`:
32 passed); its 4 ignored tests, `wasm_scaling` among them, were not run, so what the extra constructor costs existing
programs is unmeasured here (`wasm_scaling` is counted two sections down: about 1.1% more work). The `tatic` run was filtered to `gate`, `fragment` and `wasm` (`2026-11-10-call-ins-regress`:
10 gate tests, 1 fragment test and 6 tatic-wasm tests pass; 3 ignored `measure_*` tests not run).

The callee's body is a program built by `prog` from `[x]` to `[answer]` over a dummy base. Its argument and result
pass on the stack, and it has no locals: the bodies use `Dup`. A module's meaning is `N H (\x h k. z) Bm` with
`Bm = \env x h k. M_env (prog body) (x, 0) h`, and the answer is passed to `k` with its heap.

**The statement carries a state.** The source threads the cell's value `st` explicitly. Its continuation takes the
answer and the state. The heap and the state are linked by `Inv h st = Pi kk. h A kk = kk st` for the one cell `A`.
For every fuel `N` with `GoodNat N`, and every `R`, `z`, `x`, `h`, `st`, `km`, `ks`:
`(Pi a h st. Inv h st -> km a h = ks a st) -> Inv h st -> M_N x h km = S_N x st ks`. Three functions, each with
a call that has work after it:

- **sum:** `s x = x <= 0 ? x : x + s (x - 1)` (one call);
- **nest:** `d x = x <= 0 ? x : d (d (x - 1))` (the first call's continuation is the second call, which is in tail
  position; the machine treats it like any other call);
- **counter:** `c x = x <= 0 ? x : (mem[A] += 1; c (x - 1) + mem[A])` (it writes before the call and reads after).

Each proof is one fuel induction, still written by hand per function. The `then` branch is `rel`. The `else` branch
applies the hypothesis at each call. For the counter it also uses:

- `inv` at the read before the call, then one transitivity step;
- the hypothesis at the updated heap `upd A (st + 1) h`, whose `Inv` is `refl`, because conversion evaluates `upd` at
  the literal address;
- for the continuation, `inv` at the read after the call, composed with `rel` by transitivity.

**Conversion has no eta** (inferred here; the next section tests it directly). The machine's continuation for an inner call is `\y mu. km y mu`,
not `km`. The first nest proof passed `km` and was rejected with a type mismatch (run `2026-11-10-call-ins-spike-2`,
which stopped there, so the counter law has no result in it); passing the eta-expanded form made it check. A proof generated from the instruction list must follow the machine's continuations as
they are built. The first run (`2026-11-10-call-ins-spike`) failed to compile.

Run `2026-11-10-call-ins-spike-3` (untimed, one run, 22% load):

| check | n = 4 | n = 24 | n = 64 |
|---|---|---|---|
| sum law (proved) | 1.7 ms | 2.3 ms | 6.2 ms |
| nest law (proved) | 1.5 ms | 1.9 ms | 5.1 ms |
| counter law (proved) | 1.7 ms | 2.7 ms | 4.9 ms |
| sum, the call's argument `x - 2` (rejected) | 0.8 ms | 1.2 ms | 4.6 ms |
| sum, the call dropped (rejected) | 0.7 ms | 1.2 ms | 3.2 ms |
| nest, one call instead of two (rejected) | 0.9 ms | 1.3 ms | 3.3 ms |
| counter, no store (rejected) | 1.1 ms | 2.1 ms | 3.4 ms |
| counter, reads cell `A + 1` after the call (rejected) | 1.2 ms | 2.7 ms | 4.0 ms |
| run by `refl`: sum 3, fuel 4, answers `k0 6` | 1.2 ms | 2.4 ms | 7.5 ms |
| run by `refl`: nest 2, fuel 3, answers `k0 0` | 0.9 ms | 1.5 ms | 4.2 ms |
| run by `refl`: counter 3 from a zero cell, fuel 4, answers `k0 9` | 1.0 ms | 1.9 ms | 5.5 ms |

The same runs one fuel short time out, and the counter run answering 8 is rejected. Each of the five rejected law
controls changes only the machine's code; the source and the proof term stay those of the intended function. All five
fail with the same type-mismatch prefix, and the reason was not inspected further.

What it settles, and what stays open:

- **`call` fits the program type** as a constructor by index, with load's type and the program type's level
  unchanged. This answers the open part of the section above.
- **A heap through calls works for a fixed cell.** A state invariant joins the continuation relation. A write before a
  call and a read after it each cost one transitivity step.
- **Open:**
  - `Inv` names one literal address. Closure records allocated at addresses computed at run time need an invariant
    over a region, a separation-style statement, which was not tried here (the next section tests its first step).
  - Locals: the bodies avoid them, and per-activation frames are untested.
  - The table and `call_indirect`, and the calling convention for closures.
  - Proofs derived from the instruction list. Every proof here was written by hand per function, and the eta finding
    above constrains a generated one.

### A store at a run-time address across a call, the cost of `call`, and eta: three follow-ups (2026-11-10)

Three questions left by the section above, each a throwaway spike. The patch
`docs/superpowers/spikes/2026-11-10-frame-eta-spike.patch` applies on top of the call spike's patch; both reverted.

**Conversion has no eta, tested directly.** A kernel test (`conversion_has_no_eta`, first in the patch, kept since in
`crates/tatic-kernel/src/tests/conversion.rs`) checks
`\A B f. refl f` against `Pi A B (f : A -> B). Id(A -> B, f, f)`, which passes, and against
`Id(A -> B, f, \x. f x)`, which is rejected with a type mismatch; `def_eq` also says `f` and `\x. f x` differ (run
`2026-11-10-c3-eta`). It agrees with the code: `reduce.rs#conv_whnf` compares weak head normal forms constructor by
constructor and has no eta case. A generated proof must therefore pass continuations in exactly the form the machine
builds them, as the nest proof had to.

**What the call patch costs existing programs.** `wasm_scaling` (the existing machine checks at n = 4, 16, 32, 64,
controls at 64) was counted on the test exe built with and without the call patch, by retired instructions (run
`2026-11-10-c2-icount-aba`: `icount`, 6 runs per arm, arms in the order base, patched, base, on CPU 4). The patched
exe does about 1.1% more work: medians 654.8 M against 647.5 M and 647.0 M, best 651.9 M against 644.3 M and
644.2 M, with each arm's median within 0.5% of its best. An unrecorded first count gave the same gap (652.0 M against
644.3 M and 645.3 M). The patch adds the ninth constructor and also threads the environment through the interpreter
(`meaning_env`), and the count covers the whole process, start-up included, so neither part's share nor the extra
work per check is separated. One wall-time run per arm (`2026-11-10-c2-scaling-base`, `-patched`) moved in both
directions on single checks, up to 2.6 times on one of 0.2-0.5 ms and by a quarter on ones of 3-7 ms, which is noise
for checks this short. The other three ignored tatic-wasm tests (`a_large_check_does_not_churn_stack_segments`,
`bv_lemma_scaling_h3_d2_good_add`, `or_disjoint_scaling`) pass on the patched tree (run
`2026-11-10-d4-ignored-patched-2`; the first try, `-patched`, built main instead and does not count). They exercise
only the bit-vector encoding, not the machine, so they show the patch leaves the encoding alone and say nothing more.

**A store at an address computed at run time, across a call.** The caller stores at its argument's address and reads
it back after a call whose callee writes the next cell:

- caller `x`: `mem[x] := 5; g x; x + mem[x]`;
- callee `g y`: `mem[y + 1] := 7; y`.

Both are machine programs built through `prog` with the call spike's `call`; the callee has no calls. For every `R`,
`z`, `x` with `GoodBv x`, `h` and `k`, the caller's meaning equals `k (x + 5) (upd (x + 1) 7 (upd x 5 h))`. The load
after the call meets two equality tests on symbolic addresses, which conversion cannot decide. Two lemmas over
`GoodBv x` settle them:

- `eq x x = true`: one bit split per bit, chained by `cong1` and `trans_proof`, as in `add_identity_proof`;
- `eq (x + 1) x = false`: one split on bit 0 only. Adding 1 always flips bit 0, so once bit 0 is a literal the
  conjunction inside `eq` reduces to `false` whatever the other bits are.

The law is two J rewrites, one with each lemma, and needs no induction. `GoodBv`'s motive must land in Sort2 and
`Id(Bool0, ..)` lands in Sort1, and the kernel has no cumulativity, so the first run was rejected (run
`2026-11-10-c1-frame-spike`); the lemmas state their motive as `Pi Q:(Bool0 -> Sort1). Q b -> Q (lhs y)` and recover
the `Id` at the end. The second run (`-2`) rejected the frame law with a lambda domain mismatch; the cause, found by
reading the code rather than the log, was a callee that left two values on the stack instead of one. Run `2026-11-10-c1-frame-spike-3`
(untimed, one run, 7% load):

| check | n = 4 | n = 24 | n = 64 |
|---|---|---|---|
| `eq x x = true` (proved) | 0.22 ms | 0.73 ms | 1.83 ms |
| `eq (x + 1) x = false` (proved) | 0.14 ms | 0.48 ms | 1.56 ms |
| frame law (proved; it contains both lemmas) | 0.71 ms | 1.14 ms | 2.33 ms |
| the callee writes `y`, not `y + 1` (rejected) | 0.39 ms | 0.84 ms | 2.94 ms |
| the caller reads `x + 1` after the call (rejected) | 0.38 ms | 0.91 ms | 2.37 ms |
| the right program, proof `refl` (rejected) | 0.16 ms | 0.25 ms | 0.57 ms |

The last control shows that conversion alone does not decide the frame. The two program controls reuse the intended
proof and statement; all three fail with a type mismatch, and the reasons were not inspected further.

What it settles, and what stays open:

- **Frame steps at symbolic addresses are proofs, not conversion** (shown for one offset, `+1`, and a callee with no
  calls). Each read after a write at a run-time address costs one J with an address lemma. The lemmas have no
  rejected control of their own; only the three program-level controls above. A lemma for a literal offset is cheap when the offset flips a bit no carry can
  reach. For `+1` that is bit 0, so one split.
- **A literal offset `k` with low zero bits** needs the carry into its lowest set bit shown to be zero. That costs a
  chain over those bits, like `add_identity_proof`'s (inference; the next section runs `k = 2`: two splits).
- **Open: a region.** A recursive caller whose callees allocate at `p + 1`, `p + 2`, ... up to a depth that is only
  known at run time needs `eq (p + j) p = false` for symbolic `j` with `0 < j < 2^n`. This was framed as a carry-chain
  lemma over `lt_u` or no-overflow; the next section shows neither is needed and proves it.

### The region lemma: `p + j = p` exactly when `j = 0`, and offset `k = 2` (2026-11-10)

The question, left by the section above: can `eq (p + j) p = false` be proved for a symbolic offset `j`? Throwaway;
patch `docs/superpowers/spikes/2026-11-10-region-spike.patch`, which applies on top of the call and frame spikes'
patches; reverted.

**No overflow hypothesis is needed.** Modulo `2^n`, `p + j = p` exactly when `j = 0`, so the lemma is an equation
with no hypothesis: for all `p`, `j` with `GoodBv` witnesses, `eq (p + j) p = eq j 0`. Any `j` with `eq j 0 = false`
then gives `false` by one transitivity step. The proof opens both witnesses, one inside the other, with the
`bool_lemma` motive trick, and walks the bits once, so its size is linear in `n`. With `A_i` and `B_i` the prefix
conjunctions of the two `eq`s and `c_i` the carry, the invariant is `A_i = B_i` and `and B_i c_i = false` (while `j`'s
low bits are all zero, the carry is zero). Each step uses two four-variable bit equations proved by splitting every
variable (`lemma_k`, a generalisation of `lemma2`), and the hypotheses enter only by rewriting with `cong1` and
`trans_proof`. That is forced: an `Id(Bool0, true, false)` cannot be turned into a proof of another `Id`, because
`Bool0` is not a valid motive type for its own eliminator, so there is no ex falso to lean on.

**Offset `k = 2`.** Proved directly, it needs exactly the two splits the section above inferred, bits 0 and 1;
splitting either alone is rejected. It also follows from the region lemma at `j = 2`, since `eq 2 0` converts to
`false`. The frame law with a callee that writes `y + 2` proves with either lemma.

**Cancellation**, which disjointness of two cells at symbolic offsets needs: `eq (p + i) (p + j) = eq i j` also
proves, with the invariant `A_k = B_k` and `and B_k ci_k = and B_k cj_k` (the two carries agree while the offsets'
low bits agree) and four bit equations of up to six variables.

Run `2026-11-10-d1-region-spike` (untimed, one run, 79% load from another build, so times are rough):

| check | n = 4 | n = 64 |
|---|---|---|
| region lemma `eq (p + j) p = eq j 0` (proved) | 0.5 + 1.5 ms | 13 + 48 ms |
| `eq (x + 2) x = false`, bits 0 and 1 split (proved) | 0.1 + 0.5 ms | 0.7 + 10.6 ms |
| the same from the region lemma (proved) | 0.2 + 0.8 ms | 7.3 + 21.6 ms |
| frame law, callee writes `y + 2`, `k = 2` lemma (proved) | 0.6 + 2.1 ms | 4.1 + 13.2 ms |
| the same with the region lemma (proved) | 1.0 + 1.7 ms | 4.8 + 27.2 ms |
| cancellation `eq (p + i) (p + j) = eq i j` (proved) | 1.0 + 6.0 ms | 515 + 116 ms |

Times are build + check. Rejected, each with a type mismatch whose first 100 characters show nothing beyond the
`Id` being compared: the region proof against `= false` (false at `j = 0`), against `eq (p + j) j = eq j 0`, and
against `sub` for `add` (a true statement, but not this proof's); the region chain with the carry invariant replaced by
`refl false`; `refl` against the true statement (conversion alone does not decide it); bit 0 or bit 1 split alone for
`k = 2`; three frame-law programs (callee writes `x`, caller reads the callee's cell `x + 2`, the `k = 1` lemma for a
`k = 2` callee); and cancellation against `= false`, against `= eq i i`, and `refl`.

- **The region lemma grows linearly** (8.5 ms check at n = 24 in a quieter iteration run, 20-48 ms at n = 64).
- **Cancellation grows faster** (about `n^2.6` from n = 24 to 64; 16.5 + 221 ms at n = 64 in the quieter run). Its build
  is most of that in the recorded run. One inference, not isolated: a subterm reused at every step is rebuilt or
  rechecked rather than shared.
- **What a heap-allocating calls milestone still needs** is now the region statement itself (an invariant over the
  cells a recursion allocates) and the generated proofs, not a lemma.

### What a signed remainder costs the gate: a probe (2026-11-10)

The question: gcd needs `rem_s`, which the machine lacks (`Op` has no row for it, and the lowering printed
`i64.rem_s` as `Raw`). What would a 64-bit remainder circuit cost the straight-line gate? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-rem-cost-spike.patch`, reverted.

**The circuit.** `Op::RemS`: both operands made non-negative by `(x ^ s) + s`, then `n` rows of restoring division,
most significant bit first, each a ripple-borrow subtract and an `n`-wide `mux`; the result takes the dividend's sign.
`Mod` got an `op_of` row, so `\a b. a % b` enters the gate. It matches `eval.rs` (`wrapping_rem`, so `MIN % -1 = 0`)
on every n = 8 pair (all 65,536, by `def_eq`) and on about 200 edge and random n = 64 pairs; the op-table test against
eval and wasmtime passes with `b = 0` skipped.

**Division by zero has no meaning yet.** `eval` returns `DivByZero` there and wasm traps; the circuit answers `x`. The
gate builds both sides from the one table, so it would accept `rem_s` by construction at `b = 0` too, and the table
test cannot check that row because neither reference has a value. Installing `Mod` needs a trap or partial-domain
story first (the machine has no trap channel; `docs/decisions/2026-11-10-v08-shape-and-any-backend.md` already notes
it for gcd).

Measured on the gate, build + check in ms (n = 8 to 32 and the first n = 64 row best of 3 in plain runs, load not
recorded; the second n = 64 row is run `2026-11-10-e4-rem-cost-2`, 74% load; `-cost`, the first attempt, failed to
launch):

| n | `a % b` | `a * b` | distinct nodes, rem / mul |
|---|---|---|---|
| 8 | 0.08 + 0.40 | 0.06 + 0.25 | 1,288 / 650 |
| 16 | 0.19 + 1.53 | 0.14 + 1.03 | 4,440 / 2,590 |
| 32 | 0.84 + 3.82 | 0.60 + 2.52 | 16,504 / 10,502 |
| 64 | 5.5 + 16.0 | 3.3 + 8.7 | 63,672 / 42,454 |
| 64 (recorded) | 3.5 + 16.2 | 4.4 + 13.1 | same |

- **It fits.** At n = 64 a remainder costs about 20 ms, 5% of the JIT path's 0.4 s, and 1.3-1.8 times a product's check;
  in an `if` arm about 29 ms against 17 ms for `*`. Two runs of the same test moved `mul` by half, so the ratio is rough.
- **Both grow quadratically**, about 4 times per doubling in nodes and check time; the remainder's `n` subtract rows
  set its size. Not profiled.
- **So gcd's cost is not the circuit.** What it lacks is the meaning at `b = 0` above, and loops through the gate.

### Calling a closure parameter: the closure convention against its source, a spike (2026-11-10)

The question: five class C terms call a closure they receive as a parameter (11 `twice`, 17 `iterate`, 27, 32, 33;
census in `docs/decisions/2026-11-10-v08-shape-and-any-backend.md`) and install today on no proof at all. Can the
lowering's convention be proved modularly: the function for every closure related to a source function, and a concrete
closure related to its source lambda, separately? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-closure-spike.patch`, which applies on top of the call-ins spike's patch;
reverted.

**The machine change.** A closure is one word: the table index in the low half, the environment pointer in the high
half (`twice.wat`). `Ins::CallIndirect` is a tenth constructor that pops the argument and the closure word, splits the
word with two bit-rewiring circuits (the real 32-bit halves at n = 64), and runs `table idx env arg mu k`, with `table
: V -> V -> V -> Mem -> (V -> Mem -> R) -> R` a new interpreter parameter. The lowering's `i64.shr_u 32` and
`i32.wrap_i64` are not rows: `wrap` is unary and every row is binary, so the split lives in the constructor, and the
spike's code (`LocalGet 0, LocalGet 0, LocalGet 1, CallIndirect, CallIndirect` for `twice`) does not print as the
golden WAT.

**The closure relation is a hypothesis of the statement**, like the induction hypothesis of a direct call:
`CR(c, f) = Pi a h km ks. (Pi y h'. km y h' = ks y) -> table (lo c) (hi c) a h km = f a ks`, for the source function
in continuation-passing form `f : V -> (V -> R) -> R`. The `twice` law is: for every table, `f`, `c`, `x` and
continuations related as above, `CR(c, f)` implies that the machine's `twice` on `(c, x)` equals `f x (\y. f y ks)`.
Its proof is two applications of the hypothesis, the inner call's relation being the hypothesis at the outer call,
with the machine's continuations written exactly as it builds them (no eta). The other side: a table whose entry 1 is
the compiled body of `\v. v + 1`, built through `prog`, satisfies `CR` for the word `(1, env 2)` and `\a ks. ks (a +
1)`; and the two compose to `twice` on that closure equals `ks ((x + 1) + 1)` (not `x + 2`, which needs an
associativity lemma, not tried).

**`iterate` (17) needs a callee that returns the caller's heap.** Its loop keeps locals in heap cells, and after the call
the machine's continuation reads and writes them, so `km y h' = ks y` fails for an arbitrary `h'`. With `CRp`, the same
relation where the callee hands back the heap it was given, the loop proves in the sum loop's fuel-matched style
against a source recursion, and the `+ 1` closure, whose table entry restores the caller's heap, satisfies `CRp`. The
loop's invariant frame is in the order its stores leave the cells, not the gate's, and the two are equal only
extensionally, so connecting this to the gate's statement needs a heap-extensionality step (not done).

Run `2026-11-10-e2-closure-spike` (untimed, one run, 48% load), n = 64 (n = 4 and 24 give the same verdicts):

| check | build + check |
|---|---|
| the split: `lo c` is the index (proved) | 0.2 + 0.4 ms |
| `twice` law (proved) | 0.4 + 4.3 ms |
| `+ 1` closure satisfies `CR` (proved) | 0.9 + 3.4 ms |
| `twice` on it is `(x + 1) + 1` (proved) | 0.9 + 5.6 ms |
| `+ 1` closure satisfies `CRp` (proved) | 0.4 + 1.5 ms |
| `iterate` law under `CRp` (proved) | 2.4 + 10.9 ms |
| `iterate` on the `+ 1` closure equals the fuel-`N` source (proved) | 2.2 + 9.6 ms |
| run by `refl`: two iterations of `+ 1` from 5, fuel 3, answers 7 (proved) | 0.7 + 14.6 ms |

Rejected, each with a type mismatch whose first 100 characters show only the inferred `Id`, and each one change from a
proved variant: the high half as the index; `twice` calling `f` once; the inner call's argument `f x + 1`; the halves
swapped in the machine's split; a table entry computing `v + 2` against the `+ 1` relation, and composing with it; the
`iterate` run claiming 8; `iterate` testing `n < 0`, calling `f` on `n`, or dropping the call.

What it settles, and what stays open:

- **The higher-order part of goal 1 has a shape**: a closure parameter is a relational hypothesis of the function's
  statement, discharged where the closure is made. Nothing else in the generator's picture changes: a closure call is
  one more call edge whose callee's law is a hypothesis instead of the induction hypothesis.
- **Heaps.** Plain `CR` lets the callee change the heap and then requires the caller to ignore it; `CRp` requires the
  callee to change nothing. Closures whose environment is a record in memory, and anything that allocates, need the
  middle: a relation between the heap before and after (the caller's cells and the record intact), in the counter
  spike's `Inv` style (reasoning, not tried). Locals kept out of the heap would remove the caller's-cells part.
- **Term 27** (`\f. f 1 + f 1 2`) uses `f` at two arities, so the lowering calls it curried, and the result of `f 1` is
  used both as a number and as a closure. A relation between a word and a first-order function cannot say that; it needs
  a relation indexed by type, or one over a universal value domain (reasoning, not tried).

### One generator for loops and calls, with locals apart from the heap: a spike (2026-11-10)

The question: every simulation proof so far was written by hand for its function. Can one procedure, with no case per
function and no match on the instruction list, produce the proof for any body built from the gate's instructions plus
`local.set`, `call` and the function's own loop, against its source recursion? And can locals leave the heap, so a
callee's frame is not a set of heap cells the caller must show intact? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-gen-spike.patch`, which applies to `e4d4ec6` on its own (it carries the call-ins
spike's machine change, not that spike's tests); reverted.

**The machine change.** The state is a pair, locals and heap. `local.get i` reads the locals component (until now it
loaded heap address `i`), and `local.set i` is a new constructor; with `call` that makes 11. The interpreter takes
three optional hooks: an environment for `call` (a fresh locals tuple, parameter 0 the popped word, the heap shared,
the caller's locals restored on return), a restart for the function's one top-level `loop` (`br 0` calls the same
environment with the current continuation), and an opaque stand-in for `choose` (below). With no hooks the meaning is
the old one, and the existing laws pass unchanged. The hooked `loop` is not the real `loop` row, which unrolls its body
`N` times: the proofs here are for the module's meaning only.

**The statement**, for every fuel `N` with `GoodNat N`, answer sort `R`, arguments `x_i`, heap `h` and continuations
`km`, `ks`: if `Pi a loc h. km a (loc, h) = ks a`, then the machine at fuel `N` from the frame `x..` over zero locals
equals the source unrolled by `N` on `x..`. The relation quantifies over the locals and the heap, not over a state:
over a state `mu`, the callee's return continuation splits `mu` with a `sigrec` that is stuck without eta (the eta
follow-up's finding again).

**The generator** (`gen_sim`) does `GoodNat`'s induction on fuel, and in the step puts both sides in weak head normal
form and walks them in lockstep as kernel terms, with five rules:

1. a machine return against a source return: the relation hypothesis;
2. a branch against a branch on the same condition: both arms, joined by J;
3. a stuck read of a parameter's slot: the slot hypothesis, then on;
4. the fuel variable applied on both sides (a `br` and a `call` are the same edge): the induction hypothesis at the
   source's arguments and the machine's state and continuation as built, with the continuation relation generated by
   walking the two continuations under fresh binders;
5. anything else: an error naming the path and what each side does.

Loop fuel and call fuel are one fixpoint, because the function's single top-level loop is the function. The walk is
untrusted; the kernel checks the proof. With the real `choose`, `whnf` unfolds a branch into the bits of its
condition and the branch structure is lost, so the proof abstracts `choose` and is applied to it, while the statement
uses the real one.

**No per-function case.** The generator file was hashed once sum, factorial, fib and a nested call (`nest`) first
passed; three functions written after that (`dbl`, `mulloop`, `mixed`) proved with the hash unchanged. Two more (`tri`,
`pow2sum`) were written before the first run and are not clean unseen cases. Run `2026-11-10-e1-gen-spike` (untimed,
one run, 38% load), build + check in ms:

| function | n = 4 | n = 24 | n = 64 |
|---|---|---|---|
| sum loop | 2.7 + 5.8 | 5.2 + 12.5 | 6.9 + 22.7 |
| factorial | 2.8 + 7.5 | 3.0 + 9.2 | 9.9 + 27.9 |
| fib | 2.9 + 12.9 | 3.3 + 9.4 | 6.2 + 26.9 |
| nest | 2.1 + 6.2 | 2.9 + 8.1 | 5.8 + 22.8 |
| tri | 2.0 + 4.9 | 2.8 + 7.8 | 4.4 + 29.4 |
| pow2sum | 3.6 + 5.9 | 5.0 + 14.0 | 11.2 + 21.3 |
| dbl (after the hash) | 2.5 + 8.2 | 5.9 + 11.4 | 5.4 + 22.3 |
| mulloop (after the hash) | 2.3 + 5.6 | 6.1 + 14.7 | 11.3 + 31.5 |
| mixed (after the hash) | 3.4 + 9.3 | 5.0 + 13.6 | 14.3 + 55.9 |

Rejected by the walk at n = 4 and 24, each with a reason naming the mutation: sum's `acc + n` as `acc - n` ("local 1
does not hold the source's argument 1"); factorial with its call dropped ("the machine returns but the source
recurses"), with `n - 2` for `n - 1`, and with its branches swapped; sum's `local.set 0` as `local.set 2`. The kernel
rejects factorial's proof checked against nest's statement (a type mismatch).

What it settles, and what stays open:

- **Proofs can be derived from the instruction list.** Every earlier simulation proof was hand-written per function;
  here one procedure covers loops, self-calls, non-tail calls and nesting. A closure call fits as rule 4 with the
  callee's law a hypothesis instead of the induction hypothesis (the closure spike above; not tried in the
  generator).
- **Locals apart from the heap** remove the caller's-cells half of the heap problem the closure spike names; callees
  here may not touch the heap at all, so the other half (a relation between heaps before and after) is untried.
- **Limits:** calls take one argument; one top-level loop, and `br` only to it; temporaries carry no hypothesis; the
  source is a small mirror of `Source::cps`, not tatic's terms. Driving it from real terms needs `Source::cps` to grow
  a self-call case and the shared `choose` hook, and the lowering to emit `local.set`, `call` and `br` in the same
  parameters-first layout (inference from the shapes, not tried; tried in the next section).

### The generator on tatic's terms and the lowering's code: a spike (2026-11-10)

The question: does the generator above carry real inputs, the specialised `Term` through `Source::cps` on one side and
the instruction list `lower_wat.rs` emits on the other, with no per-function case? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-gen-real-spike.patch`, which applies to `f9ec5e5` on its own and contains the
generator spike's patch; reverted.

**What changed.** `Source::cps` takes the kernel context and a continuation over it, holds parameters as binders, gains
a self-call case (a spine headed by the fixpoint variable: arguments left to right, then `g args (\res. k res)`) and
uses the generator's `choose` hook; the v0.7 gate calls the same `cps` with no hook, and its tests pass. The
generator's one interface change replaced its mirror source language with a source-builder closure; it was then
hashed and not edited again. The lowering's `local.get`/`local.set` of `$p{k}` and `$t{k}` map to slots `k` and
`arity + k` (its real index order), `call $f` maps to `call` only at arity 1, and any line left `Raw` stops the attempt
before a proof is built.

Run `2026-11-10-f1-real-terms-4` (untimed, about 40% load), build + check at n = 64, ms; n = 4 and 24 give the same
verdicts:

| target (census) | specialised term | n = 64 |
|---|---|---|
| sum loop A (`capturing_closure_loop`) | `rec f n acc = if n <= 0 then acc else f (n-1) (acc+n)` | 15.9 + 45.6 |
| sum loop B (`partial_application_loop`) | the same term | 13.9 + 42.2 |
| factorial | `if n <= 1 then 1 else n * f (n-1)` | 17.0 + 83.8 |
| `redundant_arithmetic_recursion` | `if n <= 0 then 0 else n*8 + 0 + f (n-1)` | 17.3 + 78.9 |
| fib | `if n < 2 then n else f (n-1) + f (n-2)` | 15.0 + 52.9 |
| direct call 13 (`twice_inc_5`) | `(\x. x+1) (5+1)` | no proof: `i32.const 0`, `call $c0` have no `Ins` |
| direct call 34 (`let_bound_factorial_10`) | `(rec ...) 10` | no proof: the same two lines |

Six terms written after the hash, parsed and lowered for real (a triangle loop, `dbl`, a multiply loop, nested
`f (f (n-2))`, a three-parameter loop, an `==`-guarded loop), prove at 28-99 ms of check; a seventh, a two-parameter
non-tail self-call, stops on `call $f` (calls take one argument). Rejected at n = 4 and 24: three operator swaps,
factorial's `<=` as `<`, two call arguments off by one or two, two branch swaps, a wrong `local.set`, a wrong base case
(each by the walk), the call replaced by a push (by the shape check), and factorial's proof against fib's statement
(by the kernel). The existing gate tests (run `-5`) and the whole `tatic-wasm` library (run `-6`) pass on the patch.

What it settles, and what stays open:

- **Real terms carry.** The five loop and self-recursion targets of the census install from emitted code through one
  unchanged generator; what blocks the rest is the machine's vocabulary, not the proof procedure.
- **The direct calls need a module.** 13 and 34 call another function with an `i32` environment pointer: a call that
  names its callee, a callee's law as a hypothesis, more than one argument, and an `i32` kind (the machine has words and
  bits only). Lines the lowering emits with no `Ins` yet, read from the lowering, not run: `i64.rem_s`, the wrapping
  division's scratch locals, `$envtmp`, `$papenv`, `call_indirect`.
- **The printer** names every slot `$p{i}`, so a temporary at `arity + k` would print as a parameter that does not
  exist; nothing emits these yet.

### Tail self-calls as `return_call`, with no `loop` or `br`: a spike (2026-11-10)

The question: `br` and `call` are one edge in the generator, and the lowering's only `loop` wraps a function for its
tail self-calls. Can tail self-calls lower to `return_call $f`, so the machine needs no `loop` or `br`? Throwaway;
patch `docs/superpowers/spikes/2026-11-10-no-loop-spike.patch`, which applies to `b092e5c` on its own and contains the
previous spike's patch; reverted.

**What changed.** The lowering emits a self-call's arguments and then `return_call $f` in tail position or `call $f`
otherwise, with no loop wrapper, staging temporaries, copy-back or `br` (`lower_wat.rs` +7 -22). The machine's `call`
takes the callee's arity (a fresh frame, parameter `i` in local `i`), and `return_call` calls the environment with the
activation's own return continuation, a new hook; one constructor per arity up to 3. The generator's walk did not
change; its one edit, before the first run, passes that hook. wasmtime 42.0.1 accepts `return_call` with its default
configuration (the repo sets none).

Run `2026-11-10-i1-no-loop-gen-real-3` (untimed, 27% load), build + check at n = 64, ms:

| case | n = 64 | case | n = 64 |
|---|---|---|---|
| sum loop A | 5.9 + 11.8 | tri | 4.9 + 13.3 |
| sum loop B | 6.1 + 13.3 | dbl | 6.3 + 17.9 |
| factorial | 7.6 + 68.0 | mulloop | 8.9 + 21.0 |
| `redundant_arithmetic_recursion` | 7.6 + 22.0 | mixed | 11.8 + 26.5 |
| fib | 6.4 + 16.6 | pow2sum (3 parameters) | 9.8 + 18.5 |
| `==`-guarded loop | 6.2 + 10.7 | two parameters, non-tail self-call | 7.0 + 13.7 |

Every case also proves at n = 4 and 24. The two-parameter non-tail self-call, which stopped on `call $f` in the
previous spike, now proves; 13 and 34 still stop on `i32.const 0`, `call $c0`. The test prints a failure list
instead of asserting; its only entries are 13 and 34, and a case is printed as proved only after the kernel accepts
it. Rejected at n = 4 and 24: operator swaps, `<=` as `<`, call arguments off by one or two, a dropped call, swapped
branches, a wrong `local.get` in the condition and in the call's argument, a wrong base case, `return_call` put for a
non-tail `call` in factorial, fib and tri, and factorial's proof against fib's statement (by the kernel). `call` put
for a tail `return_call` proves, as it should: the code is equivalent.

Run against the emitted code: the differential compile fuzz passes 7 of 7 (`-compile-fuzz`); a tail loop of 10^6
iterations returns `n(n+1)/2` (`-deep`), while the same WAT with `call` for `return_call` traps on the stack;
`tatic-wasm` passes (`-wasm-lib`). What fails until updated: all three golden WAT tests (29 files: 23 corpus, 4
fragment, 2 specialised; `-golden`), and two `tatic` tests that expect a `loop` wrapper,
`fragment_bodies_contain_no_raw` and `gate_rejects_mutations` (`-tatic-lib`).

What it settles: one recursion edge suffices, so z5's D1 (what `loop` means) can be removed instead of decided. Gone
with `loop` and `br` (grepped, not deleted): the two constructors, `shape`'s loop stack, the restart hook, `laws.rs`'s
`loop_law` and countdown checks, the printer's arms, and `strip_loop`. Fuel stays: it moves from the machine's
`meaning` into the generator's induction. Open: calls of any arity need a family of constructors or one constructor
over a frame (the spike capped arity at 3).

### Fresh addresses by construction: the allocation pointer in the state, a spike (2026-11-10)

The question: callees that allocate or read records need a relation between heaps before and after a call (the
decision file's open heap relation). Does making the allocation pointer part of the state, so fresh addresses are
fresh by construction, avoid order reasoning on 64-bit words? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-heap-state-spike.patch` (applies to `b092e5c` on its own, with the generator-on-
real-terms patch inside); reverted. Machine code is hand-written in the lowering's shape, not emitted.

**What changed.** The state is `(locals, hp, heap)`; `alloc k` returns `hp` and bumps it. The generator gained general
rules, not cases: a stuck heap read at a declared cell is rewritten by that cell's hypothesis (as rule 3 does for a
local); a store chain is walked down to the heap, deciding each address test by conversion, the region lemma or
cancellation; a test only the machine makes on an address is decided and walked down the branch it picks. Cells are
declared per function as hypotheses `h (p + off) K = K v` with the source taking `v` as a parameter; the variant with
the record's cells inside the closure relation was not built.

Run `2026-11-10-i3-heap-state-final` (untimed), build + check at n = 64, ms:

| case | n = 64 |
|---|---|
| a read at `p + 8` | 1.0 + 5.5 |
| a loop re-reading a captured cell each iteration (term 37's shape) | 8.7 + 12.1 |
| `alloc 24`, two stores, a call on the record; the callee reads it | 81.1 + 65.1 |
| the same with a header store at `q` | 111.0 + 64.2 |
| the record updated in place and passed again | 74.2 + 52.8 |
| two allocations, cells at `q` and `q + 8` | 97.3 + 58.6 |

All prove at n = 8 and 24 too, with the heap and `hp` symbolic. At n = 4 the header and two-allocation cases fail
(addresses alias in four bits); the others pass. Rejected at n = 8 and 24: a read at the wrong offset, a cell
overwritten before its read, a condition on the wrong offset, swapped store offsets, a stored value one too large,
an overwrite before a read, and a stale `hp` with two allocations. A stale `hp` with one allocation is accepted:
nothing reads the aliased cell, so nothing differs.

What it settles, and what stays open:

- **No order reasoning was needed** for addresses of the form `hp + k`, `p + k`, `hp` or `p`: the region and
  cancellation lemmas decide them. Nested sums like `(hp + 16) + 8` are not normalised and give "cannot tell".
- **Open:** a non-tail call whose continuation reads the heap (the walk after the call has no cell hypotheses), and
  reading an older record after a later allocation or store with no relation to it: both need a callee
  heap-preservation relation or order facts. Cells are declared per function by hand.

### The partial row's cost, and gcd through the generator (2026-11-10)

The question: the decision file picks a partial row for remainder (outside its domain the machine answers the
no-value answer `z`). What does the guard cost, and does gcd then install? Throwaway; patches
`docs/superpowers/spikes/2026-11-10-partial-row-spike.patch` (the rem-cost probe plus the row; applies to `b092e5c`)
and `docs/superpowers/spikes/2026-11-10-partial-row-gcd-spike.patch` (combined with the generator-on-real-terms
patch); reverted.

**What changed.** `Dom::NonZeroDivisor` has `holds(x, y)` and a kernel circuit; `shape::dom_of` is the one lookup,
read by `eval::apply_prim` (its two hand-written zero checks go), `Source::cps` and the machine. A partial row is a new
constructor, `bin` plus the domain, meaning `choose(r, dom x y, rest (op x y), z)`. The generator gained one general
rule: two sides that are the same stuck term are equal by `refl` (both answer `z` outside the domain). `eval` now
reads `jit::shape`, so the lookup belongs in `lang`.

Cost, runs `2026-11-10-i4-partial-row-cost` and `-cost-2` (untimed, 59-66% load), build + check at n = 64 in ms,
guarded against unguarded: rem in tail position 20.1 and 27.3 against 25.7 and 30.0; non-tail `(a % b) + b` 24.4
and 20.9 against 25.2 and 25.8; `(a % b) % c` 28.4 and 32.5 against 22.3 and 31.0; rem in an arm 30.0 and 36.2
against 25.8 and 35.3. At n = 64 the guard is inside the spread between samples (up to about 40%); at n = 4 the
guarded rows are higher in all 8 pairs (under 1 ms), and at n = 24 one pair is 58% higher (4.6 against 2.9 ms).

gcd (`if b == 0 then a else f b (a % b)`) installs through the generator from its real term, run
`2026-11-10-i4-partial-row-gcd-4`: 18.0 + 24.1 ms at n = 64; the two-base-case gcd 12.1 + 22.6 ms. Rejected: the
machine dropping the guard ("the machine recurses but the source branches"), the machine alone testing the wrong
operand, and rem replaced by mul or sub. Accepted, as the decision file predicts: the wrong operand on both sides,
and no guard on either; only the table test can see those (reasoning: the domain circuit then differs from `holds` at
(5, 0); the table test was not run with these mutants). The table test at b = 0 (`-table`) passes: the domain circuit
equals `holds`, eval errors and wasmtime traps exactly where `holds` is false, and where defined the three agree,
`MIN % -1` giving 0 in all.

### The heap across a non-tail call, and an older record: a spike (2026-11-10)

The question: the heap-state spike left two cases open, a non-tail call whose continuation reads the heap and an older
record read after a later allocation. Do they prove with the allocation pointer in the state, and can the per-function
cell declarations be derived? Throwaway; patch `docs/superpowers/spikes/2026-11-10-heap-continuation-spike.patch`
(applies to `28975c2`, with the heap-state patch inside); reverted. Machine code is hand-written, not emitted.

**What changed, all general.** An associativity lemma `eq ((p + i) + j) t = eq (p + (i + j)) t` (same bit-chain
technique as cancellation) lets address decisions normalise nested sums first. The closure relation `rel` gains a
premise per preserved cell: the returned heap still holds it; a return proves the premise, and a call pushes it as a
fact while the continuation is walked. `HeapSpec::derive(code, arity)` reads cells (loads at `param + literal`),
pointer parameters and preserved cells (never stored, with code after a call) off the machine code.

Runs `2026-11-10-j2a-wasm-all` (tatic-wasm 40 passed) and the checker's `-chk-j2a`, `-chk-j2a-all`, `-chk-j2a-tatic`
(76 `proof::` tests pass); build + check in ms:

| case | n = 8 | n = 24 | n = 64 |
|---|---|---|---|
| alloc r1, alloc r2, read r1's field | | | check 183 |
| three records, r1 read under `((hp + 16) + 24) + 8` | 21.5 + 74.3 | 65.3 + 464.7 | 319.4 + 9607.0 |
| non-tail call, the continuation reads a cell the callee preserves | 7.8 + 16.4 | 31.2 + 41.0 | |

Rejected at n = 8 and 24 by the generator: the non-tail call with no preserved-cell premise; the continuation reading
a cell the callee wrote; a callee overwriting the preserved cell; reading the wrong record. `derive` matches the hand
declarations in 9 of 10 cases (two of them declare nothing, so match vacuously); the exception is a pointer never
dereferenced.

What it settles, and what stays open:

- **Settled:** nested address sums need one lemma, no order facts (tested to a three-term sum; deeper is reasoning).
  A callee's preserved cells cross a non-tail call as a premise of the closure relation, the same rule as the
  statement's own cells. Cells come from the machine code, not the source term: which source values live at which
  offsets is the lowering's layout.
- **Cost:** the three-term address checks in 9.6 s at n = 64 against 0.18 s for one level; the lemma's proof size is
  what to watch.
- **Open:** a cell the callee writes and the continuation reads (needs a postcondition naming the callee's result); a
  record allocated before the call and read after it (the callee moves `hp`; reasoned route: `hp = p + D` plus
  associativity, not run).

### A closure record's cells inside the closure relation: a spike (2026-11-10)

The question: the other heap shape the survey missed. Can the closure relation itself say the record holds the
captured values, so callers that only pass a closure carry no layout? Throwaway; patch
`docs/superpowers/spikes/2026-11-10-closure-relation-cells-spike.patch` (applies to `28975c2`, with the heap-state
patch inside); reverted. Runs took seconds and were not recorded through the wrapper.

**What changed.** A constructor `call_c` calls through a record pointer; the source side is `clo a v k`. The closure
relation is a statement hypothesis: if the continuation agrees once the record is handed back intact, the machine call
agrees with the source's `clo`. The record's invariant `Inv` is either concrete (`h (p + 8) = v`, A) or an abstract
statement binder (B), so a function that only passes the record cannot see the offset. Returns must hand the
invariant back (a framed return).

All four cases prove at n = 4, 8, 24, 64 (single runs, shared machine): the closure body (1.2 + 5.4 ms at n = 64),
`clo (clo y)` with abstract (1.7 + 4.2) and concrete (1.8 + 4.6) invariants, and an allocation then a call (6.7 +
9.2). The checker's n = 64 rerun gave 3.5 + 8.0 against 2.8 + 6.0, so "same cost" is plausible, not shown. Rejected:
a wrong captured value, a cell at the wrong offset, a wrong argument, a callee that writes the record (only the framed
return sees it), a wrong offset read, a wrong body, a store between calls (both shapes), one call against two.

What it settles, and what stays open:

- **Settled:** the closure relation can carry the record's invariant. With B, a pass-through function is proved once
  for every layout; it still carries one (abstract) invariant hypothesis, so the layout is hidden, not the hypothesis.
- **B cannot** store, allocate or read the record between calls (no frame rule for an abstract invariant); A can store
  if the stored value matches the source's. Neither handles a callee that mutates the record, several records, or
  term 27's type-indexed relation.
- **Open:** term 37's shape (a loop calling a closure each iteration) was not built; the per-function proofs were
  checked separately, not composed into one theorem, which is where an `Inv` universe problem would show.

### Modules, one call constructor and an `i32` kind: a spike (2026-11-10)

The question: the S3 rung of the v0.8 decision. Do direct calls 13 and 34 install from emitted code through the
generator once a call names its callee, the callee's law is a hypothesis, one constructor covers every arity and an
`i32` kind carries the environment pointer? Throwaway; patch `docs/superpowers/spikes/2026-11-10-modules-i32-spike.patch`
(applies to `28975c2`, with the no-loop patch inside); reverted.

**What changed.** `Ins::Call(callee, kinds)` and `Ins::ReturnCall(callee, kinds)` are one constructor each whatever
the arity, taking the state sort as an explicit operand (needed for the levels; no universe change); the per-arity
constructors go. All functions share the fuel `N`; a callee's law enters the caller's proof as a hypothesis,
discharged once by the callee's own closed proof. `K::I` with `ConstI`/`GetI` is an `i32` word told apart only by
the shape rule; the environment sits at slot `arity`. `gen_module` and the gate's `sim_module` lift emitted `$c0..`
and `$f` bodies.

Runs `2026-11-10-s3-real2`, `-s3-real3`, `-s3-reg`, `-s3-reg2` and the checker's `-chk-j4-a` to `-c`, `-chk-j4-base`;
build + check at n = 24, ms: term 13 (`twice_inc_5`) 3.2 + 6.8; term 34 (`let_bound_factorial_10`) 7.7 + 15.2; term
23 (the pap self-call loop) 9.7 + 24.1; both sum loops, factorial, `redundant_arithmetic_recursion`, fib and seven
unseen terms still prove. Rejected by the generator: the wrong callee with kinds kept (13, 34, 23), arguments swapped
(23), a false callee law (13, 34); the wrong callee by name only by the stack check. The kernel rejects a module proof
against another callee. The real-term tests print their verdicts and do not assert them; the checker read the output.

What it settles, and what stays open:

- **Settled:** one call constructor for every arity fits the kernel's levels; callee laws as hypotheses carry 13, 23
  and 34. `fragment_bodies_contain_no_raw` and `gate_rejects_mutations` fail with the patch (they pass at clean HEAD;
  the entry is no longer a `Loop`, as in the no-loop spike).
- **Open:** callees are paired with `$cK` by order and arity, unverified (a swap gives a spurious rejection, never a
  false accept); no real term with two callees ran; a callee calling another callee is rejected; whether the state
  sort operand can be derived. The first two are answered in "Callees paired by the lowering's registry: a spike".

### Callees paired by the lowering's registry: a spike (2026-11-10)

The question: the modules spike paired callees with `$cK` by order of first appearance and arity. Does a real term
with several same-arity callees, called out of registration order, install, and is a swapped pairing rejected?
Throwaway; patch `docs/superpowers/spikes/2026-11-10-callee-registry-spike.patch` (applies to `b76ba93`, with the
modules patch inside); reverted.

**What changed.** `compile.rs#build` exposes the registry it already keeps: the source function term at each
combinator index, stored in `CompiledFragment`. The gate reads the pairing from it instead of guessing; each
function's callees come from its own body, so a callee calling another callee needs no new rule, and the old
rejection of that case goes. A copy of the registry's order in the gate would be wrong: it numbers head first, then
callee bodies last in, first out. The real-term tests now assert their verdicts.

Runs `2026-11-10-m2-gen-real`, `-m2-kernel4`, `-m2-full2` and the checker's `-chk-m2` (10 passed); all four terms
below have arity-1 callees and prove at n = 4 and 24 (build + check at n = 24, ms):

| term | calls in `$f` | n = 24 |
|---|---|---|
| two callees, called `$c1` then `$c0` | `$c1 $c0` | 14.4 + 30.4 |
| roles exchanged | `$c1 $c0` | 14.9 + 31.5 |
| both callees at two sites | `$c1 $c0 $c0 $c1` | 25.2 + 50.8 |
| a callee that calls another callee | `$c0 $c2 $c0 $c1` | 38.4 + 86.8 |

The checker's rerun was 3-8 times slower on a machine at 92% CPU. Every modules-spike target still proves. A swap is
refused by the generator in all 24 cases: machine calls exchanged, registry entries exchanged, or callee bodies
exchanged. Against the right proof, the kernel rejects the first and third on all four terms; it accepts the registry
swap on the three flat terms, where the statement is the same proposition (the source names its callees by their
functions, not positions), so only the generator refuses it. The specialiser inlines a pure lambda argument, so a
callee survives only when its argument holds a self-call; all four terms are shaped that way.

- **Settled:** pairing by construction from the registry, for entry-to-callee and callee-to-callee calls.
- **Open:** pap wrappers and capturing callees are refused; mutual recursion is untested (the IR check is assumed to
  exclude cycles); the full suite's 5 failures (3 golden files and the 2 tests the no-loop spike already lists) were
  not rerun on the base alone.

### A loop calling a closure through a fixed record, and one composed theorem: a spike (2026-11-10)

The question: the closure-relation spike did not build a loop that calls a closure each iteration, nor compose the
per-function proofs into one theorem. Throwaway; patch `docs/superpowers/spikes/2026-11-10-closure-loop-spike.patch`
(applies to `b76ba93`, with the closure-relation and heap-state patches inside); reverted.

**Term 37 is not that shape.** Its emitted code (run `2026-11-10-m3-t37-dump`) is a self-loop that re-reads the
captured cell (the heap-state spike's shape), a pap thunk, one `call_indirect` on a packed closure word and an
allocating entry: lifting it needs calls, an `i32` kind and bit rows for the word split. The spike hand-wrote the
asked shape instead, `iter p n acc = if n <= 0 then acc else iter p (n - 1) (clo acc)`.

Run `2026-11-10-m3-full3` and the checker's `-chk-m3`, `-chk-m3-wasm` (tatic-wasm 42 passed); single runs, shared
machine, build + check in ms:

| case | n = 8 | n = 24 | n = 64 |
|---|---|---|---|
| loop, abstract record invariant | 8.4 + 23.0 | 10.8 + 25.3 | 21.9 + 62.8 |
| loop, concrete cell | 6.3 + 19.4 | 12.2 + 19.1 | 22.1 + 41.0 |
| loop, a fresh record each iteration | 12.2 + 27.6 | 17.3 + 50.5 | 37.7 + 93.0 |
| the composed theorem (build + kernel inference) | 7.6 + 21.9 | 8.5 + 16.5 | 13.6 + 31.7 |

The loop proved against the abstract invariant composes with the closure body proved against the concrete cell into
one theorem the kernel types, once the abstract invariant is declared at Sort2 (a concrete cell lives in Type2,
because a word is a Church type, and the kernel has no cumulativity). Rejected at n = 8 and 24, asserted: a wrong
captured value, the loop clobbering the record before or after the call, the closure called on the wrong argument,
the call dropped; the kernel rejects four composition mutants (a wrong body, a wrong source, the invariant at the
wrong offset, a body that writes the record).

- **Settled:** the closure relation carries the record across iterations, and the separate proofs compose.
- **Corrected:** a store to a cell the invariant does not name, after the call, is rejected with the concrete cell
  too ("a cell's heap is neither the statement's heap nor a store over it"): the walk follows a store chain only down
  to the statement's own heap, not a heap a callee returned. The closure-relation spike's "A can store" holds only
  before a call.
- **Open:** term 37 as emitted; a callee that calls back, several records, a type-indexed relation; the composed
  statement is inferred, not written independently.

### Locals as a frame passed in, with and without the memory: a spike (2026-11-10)

The question: the state-shape survey recommended a frame of nested word pairs, read by `local.get` as a projection and
never passed back through a return, either keeping today's single memory component (l3) or dropping it (l2), and left
open how frames of different widths share one type. Throwaway, both arms on top of the modules and registry spikes;
patches `docs/superpowers/spikes/2026-11-10-frame-l3-spike.patch` and `-frame-l2-spike.patch` (each applies to
`343abc2` and carries its base); reverted.

Both arms build the frame as `V^M x V`, where M is the widest `arity + env + temps` in the module, every frame padded
with 0 to it. `local.get i` is a row whose operand projects the frame and `local.set i` rebuilds it; both reduce under
whnf because the frame is a concrete nested pair. `unpack` builds the callee's padded frame and has no `Pi R`; the
caller's frame comes back by closure in the call's continuation. l3 keeps the memory as one opaque argument
(`G A = Fr -> A -> Mem -> R`); l2 deletes it with `Store`, `Load` and `upd` (`G A = Fr -> A -> R`).

Every target and control of the base gives the same verdict in both arms: the sum loops, factorial,
`redundant_arithmetic_recursion`, fib, terms 13, 23 and 34 and the unseen terms prove at n = 4, 24 and 64 (term 23
newly at 64), the gen_real controls and the swapped two-callee pairings are rejected, and each arm's checker reran
the tests (gen_real 10 passed, tatic-wasm 37 passed, 4 ignored; runs `2026-11-10-chk-p1-l3`, `-chk-p1-l3-wasm`,
`-chk-p1-l2`, `-chk-p1-l2-real`). Padding worked for callees of different arity and environment, so no arm needed a
call row per callee.

| | base | l3 | l2 |
|---|---|---|---|
| `sim.rs` lines | 819 | 744 | 685 |
| walk rules in the generator | 5 | 4 | 4 |
| motive binders, the sum loop | 10 | 7 | (not counted) |
| build + check, direction only | 1 | about 0.5 (check, 3 alternating pairs) | about 0.4-0.5 (2.0x by the arm, 2.7x by its checker) |

The times come from a machine 53-96% busy with other sessions, untimed and uncounted, so only the direction holds (runs
`2026-11-10-l3-base-c` to `-f` against `-l3-b` to `-b3`, and `-l2-A1-real`, `-l2-A2-real` against `-l2-B3-real`;
the l3 arm's direct call 13 at n = 4 was slower than the base).

- **Settled:** locals need not live in the state. The frame deletes the stuck-slot rule, the slot hypotheses, the
  `untouched` clause, the locals and heap binders of the motive and the state's pair destructuring, in both arms; l2
  also deletes the memory with its rows (`trans` is left dead in l2). Padding to a module-wide width covers every real
  call shape tried.
- **Not deleted:** the recursion rule still reads the concrete frame's spine (a projection of a variable frame is stuck,
  with no eta), checks each parameter slot against the source argument and the padding against 0, and passes the
  temporaries to the induction hypothesis; `cont_rel`, `rel` and the numeral `d` stay; `Call` keeps its sort binders
  `S` and `A`, which index its result type (reasoned, not tried).
- **Costs of padding:** every law in a module mentions M, so a wider callee changes every function's statement, and the
  single-function gate's statement (width m) differs from the module's.
- **Open:** the memory is untested against heap writes in l3, since the generator still rejects `Store` and `Load`;
  both arms reason, untested, that the heap's return reopens a preserved-cells premise (l3: `Pres mu mu2` on `rel` and
  the callee law, with the other rules unchanged while `Mem` stays opaque; l2: the memory and its slot rule come back).
