---
status: done
---

# Bit-vector interface for the formalized target machine (design)

Status: draft. Interface and obligations only; nothing is built.

Goal: a type isomorphic to Wasm's `i32`/`i64`, defined in the kernel with no
new primitive, so the target machine can be stated over it. This document
fixes *what the machine and the source semantics need from the type*,
independent of how it is represented. Every fact below about the emitted
code was read from `src/lower_wat.rs` and `src/eval.rs` on 2026-09-30.

## 1. Ground rules

- No kernel primitive. Only `W`, `Sigma`, `Pi`, `Id`/`J`, plus the existing
  definitions `bool_ty` and `nat_ty`.
- Every operation is total. Partial Wasm operations return `Option`.
- Proofs use the interface only, never the representation, so a
  representation can be swapped without touching them.
- The numeric view (section 3) is the bridge to ordinary arithmetic. It is
  a specification, not a claim that the representation is numeric.

## 2. Sorts

`Bv32`, `Bv64` (one family `Bv n`, `n` in {32, 64}), `Bool`, `Option A`.
Comparisons yield `Bool` only: in the emitted code they appear only as an
`If` condition (`cmp_instr`, "ir::check: If carries a comparison"), so no
`Bool -> Bv` conversion is needed.

## 3. Numeric view

`toN : Bv n -> N` (unsigned) and `toZ : Bv n -> Z` (two's complement), with
`ofN`/`ofZ` the wrapping inverses. All operations below are *specified* as
equations on `toN`/`toZ`, for example
`toN (add a b) = (toN a + toN b) mod 2^n`.

## 4. Operations, and where they come from

| op | width | Wasm | used by |
|---|---|---|---|
| `lit z` | 32, 64 | `iN.const` | literals, `i64::MIN`, `-1`, table values |
| `add` `sub` `mul` | 64 | `i64.add/sub/mul` | source `Add/Sub/Mul` (`wrapping_*`) |
| `sdiv` | 64 | `i64.div_s` | source `Div`; `None` on divisor 0 **and** on `MIN / -1` |
| `srem` | 64 | `i64.rem_s` | source `Mod`; `None` on divisor 0 only (`MIN % -1 = 0`) |
| `lt_s` `le_s` `eq` | 64 | `i64.lt_s/le_s/eq` | `If` conditions, and the div wrapper's tests |
| `and` | 32 | `i32.and` | div wrapper (`eq a MIN` and `eq b -1`) |
| `shl` `shr_u` `or` | 64 | `i64.shl/shr_u/or` | closure packing and unpacking |
| `wrap` | 64 to 32 | `i32.wrap_i64` | unpacking |
| `extend_u` | 32 to 64 | `i64.extend_i32_u` | packing |
| `add` `sub` `mul` `udiv` `gt_u` | 32 | `i32.*` | the bump allocator, `$hp` arithmetic |

Not needed: floats, SIMD, 8/16-bit access, bulk memory, `i64.eqz`.
Shift counts are masked by the width in Wasm; the emitted code only shifts
by the constant 32.

## 5. Obligations, grouped by consumer

**Source side.** None beyond the definitions. `eval.rs`'s `wrapping_*`
operators become the interface's own `add`, `sub`, `mul`, `sdiv`, `srem`, so
the source and machine use the same functions and agree by definition. The
`DivByZero` and trap cases both map to `None`.

**Division wrapper** (`emit_wrapping_div`). The emitted sequence is
`if a = MIN and b = -1 then MIN else div_s a b`.
- D1: `sdiv a b = None` iff `b = 0` or (`a = MIN` and `b = -1`).
- D2: for every other `a`, `b`, `sdiv a b = Some (wrapping_div a b)`.
- D3: `wrapping_div MIN (-1) = MIN`.
Case analysis on the two `eq` results; `MIN` and `-1` are literals.

**Closure packing** (`MakeClosure`, `MakePap`, `CallUnknown`). A closure is
`or (shl (extend_u p) 32) (lit i)`.
- P1: `wrap (pack p i) = i` when `i` is a table index.
- P2: `wrap (shr_u (pack p i) 32) = p`.
Both follow from: `or` of operands with disjoint bit ranges equals their
sum, `wrap` is `mod 2^32`, `extend_u` is the identity on values below 2^32.

**Address arithmetic and the allocator** (`emit_allocator`). The only 32-bit
arithmetic. It needs the homomorphism laws for `add`, `sub`, `mul`, `udiv`
and `gt_u` on `Bv32`, plus range side conditions: `$hp + n` does not wrap,
and `memory.size * 65536` does not wrap. The second one fails at 65536 pages
(4 GiB); whether the runtime's memory limit prevents this was not
investigated. A proof of the allocator either finds this edge or assumes a
bound.

**Memory** (separate interface, listed for completeness). `load64`/`store64`
at a `Bv32` address: read-over-write at the same address, and at addresses
at least 8 apart. Needs the numeric view for the distance condition.

## 6. Representation-independent obligations (proved once, in the library)

- H1: `toN` homomorphism for `add`, `sub`, `mul` (mod 2^n), `udiv`, `gt_u`.
- H2: `toZ` for `sdiv`, `srem`, `lt_s`, `le_s` on the non-overflow cases.
- H3: `eq a b = true` iff `a = b` (in the kernel's `Id`).
- H4: `toN (or a b) = toN a + toN b` when the bit ranges are disjoint;
  `toN (shl a k) = toN a * 2^k mod 2^n`; `toN (shr_u a k) = toN a / 2^k`.
- H5: `wrap`/`extend_u` as `mod 2^32` and identity on small values.
- H6: `lit` computes: `toN (lit z) = z mod 2^n`, by `refl` on literals.

## 7. Revisit: what this says about the representation choice

(Rewritten 2026-09-30 after sections 11 to 17; the first version assumed
`Bool` and `Nat` compute by `conv`, which is false for the kernel's postulated
`Bool` and `bool_rec`.)

1. **The lemma load is smaller than assumed.** Source-side i64 arithmetic needs
   no laws, because the source and the machine share the functions. Numeric
   reasoning is needed for 32-bit pointer arithmetic (section 5, allocator),
   for packing (P1, P2) and for the division wrapper.
2. **Representation chosen for now: a Church tuple of Church `Bool`s** (section
   13), width in the type, with `Good*` witnesses for induction (sections 12,
   16, 17). It needs no kernel change, and concrete arithmetic computes by
   `def_eq`. A bit list was dropped: a Church list cannot fold one list into the
   other (universe), and an inductive list needs a computing `Bool` eliminator.
3. **Measured cost:** a concrete 64-bit `add` is about 0.6 s and the universal
   lemma `add x 0 = x` about 33 s at n = 64 (8 bits: 70 ms), both roughly n^3,
   cause not found (section 13). This, not proof complexity, is the current
   limit. Fixing it is the gate for 64-bit work.
4. **A lever outside the type:** simplifying the emitted allocator (for
   instance growing by a fixed number of pages) would remove the 32-bit `mul` and
   `udiv` from the proof obligations. A change to `lower_wat.rs`, not yet made.
5. **Alternatives not taken:** a primitive `Bool` with iota rules (a trusted-kernel
   change; the kernel's predicativity note does not rule it out, section 11);
   binary naturals with mod (H4 bitwise is the hard part); a fixed tuple of a
   computing `Bool` (same as the chosen one, with a primitive).

## 8. Open questions

- Is a 4 GiB memory reachable in a JIT'd call (section 5, allocator)?
- Does the machine need `memory.grow` failure (`-1`) modelled, or can it be
  ruled out by a stated memory bound?
- Sign handling: model `Bv n` unsigned and derive `toZ`, or carry both?

## 9. The isomorphism record (superseded in part)

Originally: a unary `Nat` above and `Bv64` below, joined by an iso record.
**Status:** the iso record itself (R1 to R3 and the homomorphisms below) is
still the right specification, but unary `Nat` as the high-level side fails
the first of the original "four conditions": concrete small arithmetic does
not reduce in the current kernel (section 11). With Church `Nat`
(section 12) small concrete arithmetic does compute (`add 2 2 = 4`), but a
64-bit magnitude is still out of reach by computation, so big literals stay
compressed and big arithmetic goes through proven lemmas. Not built.

Let `M = 2^64`.
- R1: `toN b < M`. R2: `toN (ofN n) = n mod M`. R3: `ofN (toN b) = b`.
- Homomorphisms (statements about `Nat`): `toN (add a b) = (toN a + toN b) mod M`;
  `toN (sub a b) = (toN a + (M - toN b)) mod M`; `toN (mul a b) = (toN a * toN b) mod M`;
  `toN (udiv a b) = toN a / toN b` for `toN b > 0`; `lt_u a b = (toN a < toN b)`.
- Signed view: flip the top bit, `lt_s a b = lt_u (a + 2^63) (b + 2^63)`;
  `sdiv`/`srem` via a magnitude and a sign bit (D1 to D3, section 5).
- Packing (P1, P2) as `Nat` algebra: `(p * 2^32 + i) / 2^32 = p` and
  `(p * 2^32 + i) mod 2^32 = i` for `i < 2^32`, by induction over a symbolic `p`.
- Compressed literals (doubling DAG `g_k`) must be built closed: `shift` and
  `instantiate` skip closed subterms, `==` and `Debug` are DAG-unaware
  (section 11).
- Not covered: general bitwise ops on big concrete values; the emitted code
  only needs `or` on disjoint ranges and `and` on 0/1 values.

## 10. Sketch: a database of equivalence lemmas (Rupicola-style)

Design only. See RELATED_WORK.md section 75 for the source.

**Rule.** `(pattern, replacement, lemma)`: a pattern over `Term` with
metavariables, its replacement, and a closed kernel proof
`forall xs. Id(T, lhs xs, rhs xs)`, proved once per thread and cached like the
arithmetic prelude (section 69).

**Where it plugs in.** `specialise.rs` already emits an untrusted trace that
`spec_check.rs` replays. A rule application becomes one more step kind, named
by its rule. The checker instantiates the lemma by the match and has the kernel
check the instance, so these steps are kernel-checked where the existing
beta-v steps are certificate-checked (RELATED_WORK.md section 37).

**Matching.** `Term` nodes are hash-consed, so index rules by head operator
and literal shape and try only matching rules at each node, innermost first,
with a step cap like `MAX_STEPS`. No backtracking at first. A machine-level
choice (two lowerings of the same node) is picked by a static cost table.

**First rules** (each must survive the kernel, which is the point):
- `x + 0 = x`, `x * 1 = x`, `x - 0 = x`: no dependency beyond the definitions.
- `x * 2^k` lowered as `shl x k`: needs the `shl` law (H4) and the iso
  homomorphisms; a machine-level rewrite, since `Term` has no shift.
- `x / 2^k` lowered as `shr_s`: **false for negative `x`** (truncation vs.
  floor), so the lemma needs a non-negativity premise or must be rejected.
  Kept on the list to show the kernel refusing an unsound rule.

**Costs and unknowns.**
- Matching runs on the cold path (about 6 to 12 ms today), so it must be
  indexed and capped; measure before adding any rule.
- Lemmas are proved once, but each costs kernel time at startup.
- Loop shapes stay as they are: one universal lemma per shape, invariant on
  the high-level side, as Rupicola does for folds and ranges.
- Open: where machine-level rewrites live, since the IR (`ir.rs`) is
  representation-neutral and the templates are in `lower_wat.rs`.

## 11. Correction: `Bool` and `Nat` do not compute in the current kernel

Found 2026-09-30 by reading `NatPostulates` (`src/kernel.rs`) and confirmed
with a throwaway probe (deleted; not committed).

- `Nat := W(Bool, ChildTy)` is built over *postulated* `Bool`, `Unit`, `Empty`.
  `bool_rec` is postulated and has no reduction rule. Its computation rules
  are propositional `Id` axioms (`bool_rec_true_eq`, `bool_rec_false_eq`).
- `zero` and `succ` build their child functions with `transport`/`cong1`
  along postulated `Id` axioms, so those functions are stuck terms.
- Probe: for `one = succ zero`, `whnf(child_fn(star))` does not reach a `Sup`,
  and `def_eq(child_fn(star), zero)` is `false`.
- The existing test `nat_via_w_is_a_genuinely_computing_inductive_type` shows
  only the identity recursor reducing; it notes `is_zero(Zero) = true` needs
  one explicit propositional step.

Consequences. Anything that branches on `Bool` (`add` by recursion on a
flag, `is_zero`, `or`, `eq`) does not reduce under `conv`. So "compute by
`refl`" holds for neither the bit list nor unary `Nat` here, and the four
conditions in section 9 fail already at condition 2 (small concrete
arithmetic). Section 7 point 2 (how cheaply `add` computes) is moot until one
of these is chosen:

| option | pros | cons |
|---|---|---|
| a. computing `Bool` (eliminator with reduction rules) in the kernel | concrete arithmetic by `refl`; unblocks everything above | trusted-kernel change, needs explicit go-ahead; the kernel note says deriving base types is a predicativity dead end, so this is a new primitive, contrary to the goal |
| b. propositional rewriting proofs per step | no kernel change | proof size proportional to steps; no `refl` instance proofs |
| c. keep postulated `Int` with lemma bridges (today's `proof.rs`) | works now | the machine type is not defined, only postulated |

No choice made.

Also from the same pass (read-only audit):
- DAG-aware already (pointer-keyed memo): `whnf`, `nf`, `infer`,
  `abstract_frees`.
- DAG-unaware: `Expr ==` (`same_shape`; `Rc` short-circuits on pointer
  identity only, so two equal-shaped but distinct-pointer compressed
  literals compare in time proportional to the expanded size) and the
  `Debug` printer. Compressed literals therefore need a canonical pointer
  per value (a memo table) and must not reach error-message printing.
  `shift`/`instantiate` were not audited.
- Allocator: `memory.size * 65536` wraps to 0 at 65536 pages (4 GiB). By
  analysis, the extra `memory.grow` that results fails harmlessly, and the
  failure that matters is `$hp + n` wrapping, which ends in an out-of-bounds
  trap, not a wrong value. Not tested (needs 4 GiB). `jit.rs` sets no memory
  limiter, and a trap maps to `EvalError::Trap`.

**Does the kernel's predicativity note rule out option (a)?** Read against
`src/kernel.rs` lines 1496-1503: no. The note is about *deriving* a base type
from nothing (a vacuous eliminator would need `Pi x:Sort m. x`, one universe
too high). A `Bool` taken as a primitive with a large eliminator and iota rules
(`bool_rec C t f true -> t`) is the same move the kernel already makes for `W`
and `Sigma`, and is what the note says real kernels do. With it, `ChildTy`
would reduce and `zero`/`succ` children become ordinary `Sup` values, so the
W-built `Nat` would compute. Cost: one more `Expr` variant, its typing rule,
a `whnf_step` rule and `same_shape`/`shift`/`instantiate` cases, all in the
trusted kernel. This is a reading of the note, not a checked proof; nothing
was changed.

Allocator test added (`alloc_past_a_refused_grow_hands_out_an_out_of_bounds_block`
in `src/lower_wat.rs`): with a 2-page store limit, the second 100 KB `alloc`
returns a pointer whose block lies past the end of memory, so any access
traps. Mutation check: a 8-page cap makes it fail. It models a refused grow,
not the `i32` wrap itself.

**`shift`/`instantiate` audit** (read 2026-09-30, `src/kernel.rs` 560-680).
Neither memoizes by pointer, but both return a subterm unchanged when its
cached loose-variable range is at or below the current depth
(`loose_of(e) <= cutoff`, `x.loose() <= d`). A *closed* compressed literal
(`g_64 zero`, no free variables) is therefore returned by pointer in O(1).
Only an *open* shared DAG (a doubling term that mentions a bound variable)
would be walked unmemoised. Rule for compressed literals: build them closed,
and pass the variable in as an argument, never inside the DAG. `is_var_free`
has the same early exit. Not tested with a live doubling DAG.

## 12. Church encodings work on the current kernel (tested)

`tests/church_encoding.rs` builds everything below from `Pi`/`Lam`/`Sigma`/`Id`/`W`
alone, with no kernel change, and passes. It also rejects the false
equalities (`and true false = true`, `add 2 2 = 5`), so `def_eq` is not
trivially true.

- Church `Bool` at `Sort0`: `and true false = false` and `and true true = true`
  by `def_eq`.
- Church `Nat` at `Sort0`: `add 2 2 = 4` by `def_eq`.
- Induction witness: `Good n := Pi P:(Nat->Sort0). P zero -> (Pi m. P m -> P (succ m)) -> P n`.
  `good_zero : Good zero` and `good_succ : Pi n. Good n -> Good (succ n)`
  typecheck, and `good3 : Good 3` checks. The dependent recursor's computation
  rule holds by `def_eq`: `good3 P h0 hs` equals `hs 2 (hs 1 (hs 0 h0))`.
- `Sigma(Nat, Good)` typechecks, and `(zero, good_zero)` inhabits it.
- The W tag: `Bool` at `Sort2`, `unit := Id(Nat, zero, zero)`,
  `empty := W(unit, \_.unit)`, `ChildTy := \b. b Sort1 unit empty` typechecks,
  `ChildTy true = unit` and `ChildTy false = empty` by `def_eq`, and
  `W(Bool, ChildTy)` typechecks.

Level finding: no closed type exists at `Sort0` (any `Pi` over `Sort0` is at
`Sort1`, and `Id(A, ..)` sits at the level of `A`'s sort), so the working
universe is `Sort1`. The first attempt with `unit := Id(Sort1, Sort0, Sort0)` failed
for that reason (inferred `Type2`, expected `Type0`).

Not yet tested: equality of two `Sigma(Nat, Good)` values (needs equal
goodness proofs, no proof irrelevance), `WRec` eliminating `empty` into a
fixed type, `zero`/`succ` of the W-built `Nat`, and a `Bv64` built from
Church `Bool`s. Section 11's options A and B are therefore feasible as far as
tested; option (a), a primitive `Bool`, is not needed for concrete computation.

## 13. `Bv` as a Church tuple of Church `Bool`s (tested)

`tests/church_bv.rs`: `Bv n := Pi C:Sort1. (Bool -> ... -> Bool -> C) -> C`
(bits least significant first), literals `\C k. k b0 .. b(n-1)`, and an
unrolled ripple-carry `add` (generated by Rust, typechecked by the kernel).
Concrete sums hold by `def_eq` at n = 8 and n = 64, wrong sums are rejected.
A Church list does not work for `add`: folding one list into the other needs
to eliminate into the list's own (higher) universe, so a fixed-width tuple is
used instead, and width is part of the type.

Cost (machine at ~98% CPU, so inflated): typecheck of `add` 2 ms (n=8) and
9 ms (n=64); one concrete add 2 ms (n=8) and ~0.8 s (n=64). The 400x for 8x
the width is superlinear (roughly n^3). Suspect: carries are referenced
twice per position and beta copies them. Not profiled. The 64-bit case is an
`#[ignore]`d test. Re-measure on a quiet machine before reading anything
into the absolute numbers.

## 14. Census of the first three rules over the corpus

`tests/rule_match_census.rs` counts pattern matches (not proofs) over the 18
corpus builders, static, over hash-consed nodes: 272 unique nodes, 49 `Prim`
nodes; `x+0`: 0, `x*1`: 0, `x*2^k`: 1 (in `straight_line`). Consequences:
- A matcher that visits every node once costs at most 272 visits over the
  whole corpus (largest term: 24 nodes), so search cost is not the risk here.
- The three rules would change nothing on the current corpus except one
  multiply. Their value can only be shown on new benchmark terms that contain
  such patterns; the corpus was written without them. Before building the
  database, add a benchmark where a rewrite matters (for instance strength
  reduction in a hot loop), or the database is unmeasurable.
- `Term` has no shift, so the `x*2^k` rule is a machine-level rewrite
  (section 10, open question), not a `Term` rewrite.

**Where the `add` cost goes (2026-09-30, machine at ~47% CPU).** `normalize`
of one concrete add, by width: 8 bits 1.1 ms, 16: 11 ms, 32: 80 ms, 48: 250 ms
(about n^3). Findings:
- The tuple skeleton alone (a and b unpacked, sums set to a constant) is n^2:
  2.6 ms at 64 bits. With `xor(a_i, b_i)` sums and no carry, 6.5 ms. So the
  carry chain accounts for essentially all the cost.
- Two fixes were tried and did not change the exponent: binding each carry
  once with `(\c. rest) carry` (about 25% faster, still ~n^3), and making the
  carry the once-used operand of `xor` (no change). So "carry used twice per
  position" is not the main cause.
- Cause not identified. Next tool: a whnf/instantiate step counter in the
  kernel (a change to `kernel.rs`, so it needs a go-ahead), or a sampling
  profiler. Also untried: a balanced-tree tuple, a carry-select adder, and
  checking that the test's terms are pointer-shared the way the kernel's
  memo expects.
- Until then 64-bit concrete `add` at ~0.6 s is unusable on a JIT cold path;
  only one-off instance checks are affordable.

**Benchmark with a rewrite to win.** `redundant_arithmetic_recursion` in
`benches/common.rs` (`rec f n = if n <= 0 then 0 else n*8 + 0 + f(n-1)`)
holds one `x+0` and one `x*2^k`; it compiles, and the census now reads 286
nodes, 54 prims, `x+0` 1, `x*1` 0, `x*2^k` 2. It is not yet in the criterion
benches or the golden WAT list (the latter needs a regenerated snapshot).

## 15. Pair equality and `Empty -> Nat` (tested, `tests/church_encoding.rs`)

- Two routes to `Good 1` (`good_succ 0 good_zero` and a hand-written
  `\P h0 hs. hs 0 h0`) are definitionally equal, and so are the pairs built
  from them. Canonical proofs therefore cost nothing in concrete equalities.
- A symbolic proof `g : Good n` is **not** definitionally its eta-expansion
  `\P h0 hs. g P h0 hs`, as predicted (no eta in the kernel). Equalities between
  pairs with symbolic goodness proofs need a lemma.
- `Empty -> Nat` typechecks as `WRec` with a constant motive and step
  `\u f ih. ih tt`, with `tt := refl zero`. So `zero`'s empty child function
  does not need a postulate.

## 16. First universal lemmas (tested, `tests/church_lemmas.rs`)

For a symbolic Church bit `a` with a `GoodBool a` witness
(`Pi P:(Bool -> Sort1). P true -> P false -> P a`), both per-bit facts behind
`x + 0 = x` typecheck on the unchanged kernel, each as a two-case proof
`g motive (refl ..) (refl ..)`:
- sum bit: `xor(xor(a, false), false) = a`;
- carry out with `b = 0`: `or(and(a, false), and(false, xor(a, false))) = false`.
A false statement (`xor(a, false) = false`) is rejected.

Level note: `Id` over `Bool` lives in `Sort1`, so the induction motive must
range into `Sort1`, not `Sort0`. `GoodBool` is therefore one universe up from
`GoodNat` in section 12 (which never used `Id`).

Not done, and the real remaining gap: assembling the `n` bits into
`add x zero = x` for a symbolic tuple `x`. The tuple needs its own
witness (`GoodBv x`, induction over the tuple constructor) because there is no
eta, and the per-bit lemmas must then be combined through `Id` congruence over
`n` positions. Expect proof size linear in `n` and the kernel cost to show in
the same n^2 to n^3 range measured in section 13 (not measured for proofs).

## 17. `add x 0 = x` for a symbolic 2-bit vector (tested)

`tests/church_bv.rs`, `add_zero_is_the_identity_on_a_symbolic_good_two_bit_vector`:
`Pi x:Bv2. GoodBv x -> Id(Bv2, add x zero, x)` checks on the unchanged kernel
in about 2 ms, where `GoodBv x := Pi P:(Bv2 -> Sort2). (Pi a0 a1. GoodBool a0 ->
GoodBool a1 -> P (mk a0 a1)) -> P x`. The proof applies `x`'s own witness to
the motive, then for symbolic good bits `a0`, `a1` combines the per-bit
lemmas of section 16 with `cong1`, `trans_proof` and `cong_n` (congruence
over the two tuple positions). `good_mk : GoodBool a0 -> GoodBool a1 ->
GoodBv (mk a0 a1)` also checks, so canonical tuples have witnesses. The same
proof shape is rejected for `add x 1 = x`.

Shape of the cost: the proof has one per-bit lemma use per position, plus
`cong_n` with `n` steps, so its size is linear in `n`; the conversion checks
inside it (`add (mk a0 a1) zero` against the tuple) are the `add` evaluation
of section 13, which was n^3 in concrete use. Not measured beyond n = 2.
Next: n = 4 and n = 8 to see the growth, then a generator (Rust builds the
n-position proof) rather than hand-written terms.

> **Stale timings (2026-10-04).** Sections 18-29 (the n^3 growth, 14-20 s at n=64, the L1 prototype and the NbE status) were measured before sections 51-81 (relevance-keyed infer memo, shared shifts in the proof builder, hash-consing, scoped interning). `add x 0 = x` now checks in about 0.13 s at n=64 (`shared_carry_scaling`, research notes section 90b); section 27's commutativity point was never run at 64. Read these sections as the history of how the cost was found, not as current numbers.

## 18. Scaling of the universal `add x 0 = x` lemma (tested)

`add_zero_proof(n, 0)` in `tests/church_bv.rs` is generated from Rust for any
width, and checks for n = 1, 2, 3, 4, 8 (the same proof is rejected against
`add x 1 = x` at each). Check time, machine at 50% to 80% CPU so inflated:
n = 8: 70 ms, 16: 0.49 s, 32: 3.4 s, 64: 32.6 s, about n^3 (each doubling 7x to
10x). Proof size is linear in n, so the cost is the conversion work, the same
suspect as the concrete `add` (section 13). The 64-bit case is out of reach on a
cold path until that is fixed, but fine for a one-time lemma at startup if it
were cached.

**Second lemma: left identity.** `add zero x = x` is generated by the same
function with the operands swapped (`add_identity_proof(n, 0, true)`), and
checks at n = 1, 2, 3, 4, 8 (8 bits: about 50 ms, like the right identity). Its
mutation `add 1 x = x` is rejected. So the pattern (a `GoodBv` witness, per-bit
lemmas, a carry chain rewritten to `false`, `cong_n` over the positions)
carried over with about ten changed lines. Not yet tried: a lemma where the
carry is not always false, such as commutativity.

## 19. The n^3 cause, from kernel call counters (2026-09-30)

Temporary counters in `kernel.rs` (`whnf_step`, beta, `instantiate`, `shift`
calls; edit reverted, never committed), run on the concrete 8/16/32-bit `add`
(`add(n)`, non-shared carries) and on the universal `add x 0 = x` check:

| | whnf_step | beta | instantiate | shift |
|---|---|---|---|---|
| concrete n=8 | 1,510 | 723 | 8,876 | 3,325 |
| concrete n=16 | 5,400 | 2,734 | 45,914 | 22,182 |
| concrete n=32 | 20,212 | 10,560 | 271,002 | 160,792 |
| lemma n=8 | 120,658 | 862 | 188,601 | 116,542 |
| lemma n=16 | 605,002 | 2,270 | 1,303,205 | 602,250 |
| lemma n=32 | 3,397,690 | 6,622 | 10,881,789 | 3,439,714 |

Reading: reduction steps and betas grow about n^2 (each doubling 3.7x), but
`instantiate` and `shift` calls grow faster (5x to 8x per doubling) and time
tracks them (about 180 ns per call). Instantiate calls per beta rise from 12
(n=8) to 17 to 26 (n=32), so **each beta walks a body that grows with n**.
Cause: the carry chain is a shared DAG (c_i is used in s_i and in c_(i+1)) but
`instantiate` has no pointer memo and walks it as a tree, so the body is
O(n^2) nodes and there are O(n) betas: O(n^3). The kernel's earlier audit
(section 11) said `instantiate` only skips *closed* subterms; here the
body mentions loose bit variables, so nothing is skipped. (Counter caveat:
the counters count entries, including early exits on closed terms, so `shift`
counts substituted occurrences, not work.)

**Superseded by section 20: this fix was tried and made things slower.**

Fix proposed here (trusted-kernel, performance only): memoise `instantiate`
by (node pointer, depth) for one call, as `abstract_frees` already does
(`FreesMemo`, `RELATED_WORK.md` §63). Expected effect: the shared carry DAG is
walked once per beta, O(n) instead of O(n^2), so `add` and the lemma drop
from n^3 to about n^2. The same applies to `shift`. Needs: your go-ahead, a
test that substitution results are unchanged (compare memoised and plain on
the corpus and on the Church terms), and a mutation check.

## 20. The memo did not help; profile of the lemma (2026-09-30)

**Memoising `instantiate` was tried and is not adopted.** `instantiate` kept a
per-call map keyed by (node pointer, depth), skipped for uniquely owned
nodes. A test that a 2^k-path DAG stays k+1 nodes failed before the change
and passed after; all 77 kernel tests and the random comparison against the
reference `instantiate` passed. But the lemma got slower, in the same
(debug) profile, back to back, with another session at about 37% CPU and
Defender real-time protection off:

| `add x 0 = x` | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| no memo | 0.26 s | 1.47 s | 7.9 s | 84 s |
| memo | 0.37 s | 2.49 s | 12.8 s | 121 s |

The change is reverted (kernel clean). So section 19's conclusion, that
`instantiate` walking a shared DAG as a tree is the n^3 cause, is wrong or
incomplete: the counters showed it is DAG-unaware, not that it dominates.

**Profile** (`samply` records on Windows via xperf; its names come out as
`fun_<rva>` and were resolved with `llvm-symbolizer` against the PDB). Whole
scaling test, n=8..64, so n=64 dominates.

Debug build: 64% of samples under `check`/`infer`; dropping `Expr` trees
about 25% inclusive; `instantiate` about 20%; `whnf_step` about 10%; `conv`
about 9% (`eq_noting` 6%); `shift` about 5%; stack-guard bookkeeping
(`stack_ok`, `FLOOR`) about 10% self, which release removes.

Release build (`CARGO_PROFILE_RELEASE_DEBUG=true`; times match the recorded
ones: 75 ms, 0.59 s, 3.9 s, 34.9 s):

| Share of samples | |
|---|---|
| `drop_glue<Expr>` inclusive | 35% (20.6% self; `RtlFreeHeap` 9.5% self) |
| dropping the `HashMap<PtrKey, Rc<Expr>>` caches | 25% inclusive |
| `infer_rc` self (cache lookups) | 14% |
| `def_eq` inclusive | 39% |
| `instantiate` self | 8% |
| `shift` inclusive | 7% |

Reading: **the dominant cost is allocating and freeing `Expr` nodes, not
walking them.** A quarter of the time is freeing the per-call caches, which
hold an `Rc` to every intermediate result, so the cost of every substituted
body is paid again at teardown. Memoising `instantiate` adds hashing and more
retained nodes and saves little of this. A fix has to allocate fewer nodes
(lazy substitution in `whnf`, so beta does not build a body), or make freeing
cheap (an arena per call), or retain less in the caches. None is applied.
Caveats: release inlining hides some attribution (`instantiate` mostly shows
as its closure), and profiles include n=8..32 runs, dominated by n=64.

## 21. The lemma timings ran on the system heap; mimalloc (2026-09-30)

The lib's `#[global_allocator]` (mimalloc) is `#[cfg(test)]`, so integration
tests such as `tests/church_bv.rs` ran on the Windows system heap; the
profile in section 20 showed `Rc<Node>` alloc/free going straight to
`RtlAllocateHeap`/`RtlFreeHeap`. `tests/church_bv.rs` now declares the same
mimalloc `#[global_allocator]` `main.rs` ships with. Release build, unprofiled,
back to back, one run each, CPU about 37% from another session, Defender
real-time protection off:

| `add x 0 = x` | n=8 | n=16 | n=32 | n=64 |
|---|---|---|---|---|
| system heap | 66 ms | 0.52 s | 4.2 s | 34.7 s |
| mimalloc | 99 ms | 0.52 s | 2.1 s | 19.3 s |

About 1.8x to 2x faster at n=32 and 64, equal at 16, slower at 8 (single-run
noise or allocator start-up; not investigated). The earlier tables in sections
18 to 20 are system-heap numbers. The growth is still about n^3 (x9 per
doubling at 64 before, x9 after): the allocator cuts the constant, not the
exponent.

## 22. Profile with mimalloc (2026-09-30)

Release build with debug info, `tests/church_bv.rs` on mimalloc, `samply`
(xperf) recording the whole scaling test (8 to 64 bits; 17,951 samples, n=64
about 13.5 s of it), names resolved with `llvm-symbolizer`. CPU about 9% before
the run, Defender real-time protection off. Shares are of samples with the
named frame anywhere on the stack, so they overlap and are not savings.

| Frame on the stack | System heap (section 20) | mimalloc |
|---|---|---|
| drop (`drop_glue`, `drop_slow`, `drop_inner_table`) | 35% | 21.6% |
| dropping the cache tables | 25% | 14.2% |
| substitution (`instantiate`, `shift`, `subst_top`) | 34% | 33.1% |
| `def_eq`/`conv` | 39% | 27.9% |
| `whnf` | | 33.4% |
| mimalloc itself (`mi_*`) | | 12.7% |
| `im::vector` (the context `Ctx`) | | 15.0% |
| `InferCache` enter and hashing | | 6.7% |

Self time: `infer_rc` 15.9%, `instantiate` closure 14.0%, `drop_glue<Expr>`
10.2%, `InferCache::enter` 3.5%. Substitution under `whnf` 22.8%, outside it
(`infer`) 10.4%.

Reading: mimalloc cut the drop share and the cache teardown, as expected, but
substitution stays at a third of the samples, so the n^3 is unchanged. Two
findings are new. The context (`Ctx`, an `im::Vector<Expr>`, cloned and pushed
at every binder in `check_rc`) accounts for 15% of samples, which no earlier
option in the node-churn note addresses. `infer_rc`'s cache lookups plus
`InferCache::enter` are 6.7% and 15.9% self. Against the note's gate (stop if
drop and teardown fall under about 15%): cache teardown is 14.2%, total drop
21.6%, so it is borderline and lazy substitution (L1/L2) is not yet justified
by drop cost alone.

**Context cost, detail** (same profile, frames under `im::`, `sized_chunks`,
`ctx_lookup`): 16.3% of samples touch the context, called from `infer_node`
(7.4%) and `check_rc` (7.0%). Innermost frames: `Arc<Chunk>` 6.3%, `Chunk`
clone 3.4%, `Vector::clone` 2.7%, `ctx_lookup` 1.3%, drop 1.2%, `push_back`
0.8%, `Vector::get` 0.6%. So the cost is copy-on-write: each binder does
`ctx.clone()` then `push_back`, and pushing into a shared tail chunk copies the
chunk (an `Expr` refcount bump per entry). Lookups are cheap (under 2%). The
kernel uses only `new`, `len`, index, `clone` and `push_back` on `Ctx`
(`kernel.rs` 1100-1103 and the six clone-then-push sites); outside the kernel
it is named in `proof.rs` (45 times), `compile.rs` (6) and the tests, mostly as
`Ctx::new()`. A persistent list (O(1) push, O(depth) lookup) would remove the
copy; the lookup walk is the cost to measure.

## 23. Release flags and the context overlay (2026-09-30)

**Release flags.** `lto = "fat"`, `codegen-units = 1` (via env override, `church_bv` test build, `-j 4`, debug info off): build 1983 s against 425 s (4.7x), lemma times overlapping the baseline's (n=64: 48.7-50.7 s against 50.9-52.1 s, two runs each, machine at 92-100% CPU, Defender real-time protection off). No measurable gain, so `Cargo.toml` is unchanged.

**Context overlay.** `infer_node`/`check_rc` (and the `infer_sigma`/`infer_pair`/`infer_sigrec`/`infer_sup` helpers) now take a `&mut CtxScope` (the caller's `Ctx` plus a local `Vec` pushed and truncated in place) instead of cloning an `im::Vector` and pushing at every binder (section 22: about 15% of samples). Public `Ctx` and all callers are unchanged. Paired runs, alternating, same profile and mimalloc, CPU 40-100% from other sessions: n=32 4.51 s -> 3.80 s and 5.60 s -> 4.39 s; n=64 41.9 s -> 36.4 s and 46.7 s -> 39.0 s, about 13-22% faster in every pair. Kernel, fuzz and soundness-fuzz tests pass (343 lib tests). The exponent is unchanged.

**Cache retention (tried, reverted).** `whnf_rc` and `nf_rc` skipped the cache for nodes with `Rc::strong_count == 1` (as `infer_rc` does). The kernel test `nf_and_def_eq_are_linear_on_a_stuck_spine` fails: a stuck spine's nodes are referenced once, and re-reduction reaches them again through a rebuilt parent, so pointer-keyed hits on single-use nodes are what keeps that walk linear (section 48/59 of `RELATED_WORK.md`). Unlike `infer`, where a twice-reached node implies a shared ancestor, reduction revisits single-ref nodes. Not A/B timed: the correctness test already rules it out as written. A variant that keeps spine nodes and skips only `nf` entries was not tried.

**Quiet-machine rerun and the `nf`-only variant.** With CPU at 12-16% and Defender real-time protection off, the overlay build (same profile and mimalloc as section 21's 19.3 s) runs the lemma at n=32 in 1.63-1.68 s and n=64 in 14.0-14.5 s (section 21: 2.14 s and 19.3 s), about 25% faster. Skipping only the `nf` cache entries for single-reference nodes (keeping the `whnf` ones, so the stuck-spine test passes) gives 1.53-1.65 s and 14.3 s in alternating runs: no difference, so it is reverted. A fresh `samply` profile could not be taken: `samply record` hangs without starting a trace from this session (it worked earlier in the day, so it is probably waiting for an elevation prompt). The remaining split is unmeasured.

## 24. Profile with the context overlay (2026-09-30)

Release build with debug info, `tests/church_bv.rs` on mimalloc, `samply` (xperf) over the whole scaling test (13,569 samples; n=64 took 10.7 s while recording; CPU about 15% before, Defender real-time protection off), names resolved with `llvm-symbolizer`. The earlier `samply` hang (section 23) was transient: the same command worked on retry. Shares are of samples with the frame anywhere on the stack, so they overlap.

| Frame on the stack | Section 22 (mimalloc) | With overlay |
|---|---|---|
| `im::vector` / `Ctx` | 15.0% | 0% (`ctx_lookup` 1.0%) |
| drop | 21.6% | 21.7% |
| dropping the cache tables | 14.2% | 16.2% |
| substitution (`instantiate`, `shift`, `subst_top`) | 33.1% | 35.9% |
| `def_eq`/`conv` | 27.9% | 32.3% |
| `whnf` | 33.4% | 36.0% |
| mimalloc (`mi_*`) | 12.7% | 12.6% |
| `InferCache` enter and hashing | 6.7% | 8.2% |

Self time: `instantiate` closure 16.7%, `infer_rc` 11.8%, `drop_glue<Expr>` 10.8%, `loose_of` 6.3%, `InferCache::enter` 5.4%, `infer_node` closure 5.1%, `shift_child` 4.3%. Substitution under `whnf` 25.9%, outside it 10.0%.

Reading: the overlay removed the context cost entirely and the other shares grew only because the total shrank. What is left is substitution (36%), cache and node teardown (22%, of which the cache tables are 16%) and `def_eq` (32%, mostly the same substitution and `whnf` beneath it). `loose_of` at 6.3% self is new to the list: it is read on every `instantiate`/`shift` child to skip closed subterms, so it is the price of that early exit. `InferCache::enter` plus hashing is 8%.

## 25. The L1 prototype and where conversion time goes (2026-09-30)

`src/kernel_lazy.rs` (untrusted, not called by anything; commit `0b3d17e`) is a closure-based `def_eq_lazy`: call-by-need environments, binders as closures, comparison by applying closures to fresh de Bruijn levels, every kernel reduction rule (beta, `J` on `Refl`, `WRec` on `Sup`, `SigRec` on `Pair`) and every child the kernel's `nf` compares, binder domains included. It agrees with `kernel::def_eq` on 20,000 random pairs (the kernel's own generator and `with_redexes`; over 2,000 equal and 2,000 unequal) and on targeted cases. Mutation checks: swapping `J`'s `a` for `b`, swapping `SigRec`'s `a` and `b`, dropping the `Lam` domain comparison and dropping the `WRec` induction-hypothesis domain each fail a test (the first and last only after two targeted tests were added; the random pairs alone missed them).

**Replay of the lemma's own queries.** A scratch hook (not committed) recorded every `def_eq(inferred, expected)` that `check_rc` makes, with the context depth, and replayed them through both implementations (release, mimalloc, overlay build; the machine was at 30-100% CPU, so absolute times are noisy).

| n | queries | not syntactically equal | check |
|---|---|---|---|
| 16 | 194,367 | 141 | 0.5-0.8 s |
| 32 | 1,173,055 | 285 | 2.9-5.1 s |
| 64 | 7,841,343 | 573 | 21-33 s |

- Over 99.99% of the queries are syntactically equal, so the kernel's `==` shortcut answers them: a bare `==` over all 1.17M pairs at n=32 takes 0.11 s.
- The few other queries carry nearly all of `def_eq`'s cost: n=16, 141 queries take 0.12-0.18 s of a 0.5-0.8 s check (about 25%). At n=32, a replay with a `==` fast path in `def_eq` still took 1.6 s of the 2.2 s without it, so the 285 hard queries are about 1.5 s of a roughly 3-4 s check.
- **L1 as prototyped is 13-17x slower** on those 141 queries (2.05 s against 0.12-0.18 s), and about 25x slower on the whole n=8 (35,839 queries) and n=16 sets (no `==` shortcut), and the n=32 replay was abandoned after more than 30 CPU-minutes. The kernel's `ReductionCache` shares work by `Rc` pointer across the whole DAG; the prototype's cells share only per environment binding, so a subterm shared in the proof is evaluated again in every environment that reaches it.

Reading: lazy substitution as such does not pay here. What the kernel gets right is DAG-aware memoisation, and an NbE conversion would need its own pointer-keyed cache on `(term, environment)` to compete, which is a larger design than L1 and not justified by this result. The remaining conversion cost is O(n) queries whose terms are large, each currently a full `whnf`/`conv` over a DAG. That points at making those few queries cheaper (smaller or more shared proof terms, section 6 of the node-churn note's option S) rather than a new reducer.

## 26. Hard-query sizes, and a negative result on shrinking the proof terms

Measured by logging every `def_eq` call made from `check_rc` during the `add x 0 = x` lemma (scratch hook, reverted), then sizing the "hard" ones (inferred type `a` against expected `b`, not syntactically equal):

| n | hard queries | total tree size over hard queries | max single term (tree) |
|---|---|---|---|
| 8 | 69 | 0.61M | 38k |
| 16 | 141 | 4.6M | 133k |
| 32 | 285 | 35.3M | 485k |

The count grows about n, the max term about n^2, the total about n^3, matching the lemma's check time. The DAG is far smaller than the tree (about 11x sharing at n=32), so the cost is not the raw tree size alone.

**Experiment:** rewrote the generator so the carry and sum steps are two lemmas proved once (`cstep : Pi a c. GoodBool a -> Id(c,false) -> Id(carry(a,c),false)`, and the sum analogue), applied per position with the shared `c_i`, replacing the inlined `cong1`/`trans_proof` bodies. It checks (n up to 8, wrong statements `add x 1 = x` and `add 1 x = x` still rejected). Timing (release, mimalloc, CPU 40-70% busy from other work, so best-of-2): n=16 0.21-0.32 s, n=32 1.55-2.68 s, n=64 18.0-25.5 s, against the quiet-machine baseline of about 1.6 s and 14 s. **No gain**, so it was reverted.

Reading: the large inferred types come from the statement, not the proof body. `add(n)` inlines each carry (`c_(i+1) = carry(a_i, c_i)`, O(i) nodes), so the type of `pc_i : Id(c_i, false)` is already O(i), and any proof that mentions `c_i` carries it. Shrinking the proof cannot shrink that. The remaining options change the statement: state the lemma over `add_shared` (carries let-bound), which is a different but equally valid definition of add, at the price of proving the two equal or fixing one as the definition.

## 27. Commutativity of the unrolled adder: `add x y = add y x`

`add_comm_proof` in `tests/church_bv.rs` proves `Pi x y. GoodBv x -> GoodBv y -> Id(Bv_n, add x y, add y x)` on the unchanged kernel. Eliminate `x` then `y` with their `GoodBv` witnesses; both sides then reduce to tuples of per-bit sums with inlined carries, and the goal is `cong_n` over the per-bit equalities. Two closed lemmas do the work, both from one helper `comm_lemma(F)`:

`Pi a b c c'. GoodBool a -> GoodBool b -> Id(c, c') -> Id(F(a,b,c), F(b,a,c'))`

proved by case analysis on `a`, `b` only (4 leaves; `c`, `c'` stay symbolic, so no `Good` witness is needed for carries). Each leaf is `cong1` in the last argument, and the swap of `a`, `b` closes by conversion once they are literal bits. `F = carry` gives the carry chain `pc_i : Id(c_i, c'_i)`; `F = sum` gives the sum bits. No exponential case split over all bits.

Checks: n=1, 2, 4 pass, and the statement `add x y = add x x` is rejected both against its own proof and against this proof (test `add_is_commutative_on_symbolic_good_vectors`).

Timing (release, mimalloc, **machine 87% busy from other work**, Defender RTP off, so an upper bound; peak memory 0.32 GB at n=32, run under `memguard.ps1`): n=8 0.17 s, n=16 1.8 s, n=32 8.5 s. About 4.6x per doubling between 16 and 32 (the `add x 0 = x` lemma was about 4.6x per doubling too), so the same n^2-n^3 growth; n=64 is extrapolated at roughly 70-120 s and has not been run. Rerun on a quiet machine before quoting.

## 28. Probe: the statement over `add_shared` (statement-only change)

`add_identity_proof_over(n, rhs, left, adder)` states `add x 0 = x` over any adder; the proof body is unchanged. `add` stays the default and the one every other lemma uses, so the two definitions can still be bridged later. Tests: `add_shared_zero_is_the_identity_on_a_symbolic_good_vector` (n=1,2,4,8, with `add_shared x 1 = x` rejected) and the ignored `add_shared_zero_scaling`.

Result: it checks, and it is **not faster**. Same exe, back to back, two runs each, machine 39% busy, Defender RTP off, peak memory under 0.1 GB (best of 2 / worst of 2):

| n | `add` (original) | `add_shared` statement |
|---|---|---|
| 16 | 0.25 / 0.58 s | 0.30 / 1.04 s |
| 32 | 2.16 / 4.70 s | 1.77 / 6.21 s |
| 64 | 15.8 / 42.9 s | not run |

The two are within the noise. Reading: the proof's per-bit terms `s_i` and `pc_i` are still built with inlined carries, and conversion beta-reduces `add_shared`'s `(\c. rest) e` redexes, which substitutes each carry back in. So the unshared form is what the checker ends up comparing either way. A real test of the shared form needs the proof body shared too (carries let-bound inside the proof, with the lemma's equalities stated about the bound variable), which is a different generator, not a statement tweak.

## 29. NbE status (2026-09-30)

One place for what has been tried, since it is spread over §20-§28 and `2026-09-30-kernel-node-churn-options.md`.

| Item | State | Evidence |
|---|---|---|
| L1, closure-based `def_eq` (`src/kernel_lazy.rs`, untrusted, 7 differential/mutation tests) | built, **lost**: 13-17x slower on the n=16 hard queries, ~25x on whole query sets, n=32 replay abandoned after 30+ CPU-minutes | §25 |
| Why it lost | its thunks share per environment binding; the kernel's `ReductionCache` shares by `Rc` pointer across the DAG, so a shared subterm is re-evaluated in every environment that reaches it | §25 |
| L2, whole-checker NbE (semantic values, levels for neutrals) | **not started**; largest rewrite, new audited core | options note §6 |
| Competitive L1 (memo keyed by (term pointer, relevant environment prefix)) | spiked (§30-§32): full memo is 8-9x slower than the kernel; memoising closed nodes only (§32) reaches parity from n=32 (0.6-0.8x the kernel's time), same exponent; **thread open** | §30-§32 |
| Kernel changes taken from this line of work | context overlay only (about 25% on the lemma); nothing NbE in the trusted kernel | §23 |
| Related experiments that also lost | memoised `instantiate` (§20), cache retention skip (§23), shrinking proof bodies (§26), statement over `add_shared` (§28) | |

Why the cost is not an NbE-shaped problem so far: it sits in O(n) hard queries comparing a large inferred type against a small expected one (§26), and in node allocation and teardown (§20), not in the number of reduction steps.

## 30. Spike: pointer-shared lazy conversion (2026-09-30)

`def_eq_lazy_shared` in `src/kernel_lazy.rs` (untrusted, kernel untouched) adds the sharing §25 said a competitive NbE needs: for a node with more than one owner, `eval` and the cell built for it are memoised by (node pointer, the cells its first `loose` environment slots point to), and pairs of values already found convertible are remembered. Differential tests: `eq` in the module's tests now asserts plain and shared agree on every case, plus `shared_mode_keeps_a_doubling_dag_linear` (two independent 2^40-path DAGs compare equal; impossible without the sharing) and its differing-leaf twin.

Replay of the lemma's hard queries (same exe, cold per query, release, mimalloc, CPU 41% busy, Defender RTP off, peak 0.63 GB under `memguard`; hook in `check_rc` was scratch and reverted):

| n | hard queries | kernel `def_eq` | shared lazy | ratio |
|---|---|---|---|---|
| 8 | 69 | 4.1 ms | 75 ms | 18x |
| 16 | 141 | 76 ms | 748 ms | 10x |
| 32 | 285 | 914 ms | 7.13 s | 7.8x |

All verdicts agree with the kernel (all true). The sharing fixes the blow-up (§25's plain version did not finish n=32 in 30+ CPU-minutes), but the result is still 8-18x slower than the kernel, and the growth per doubling is about the same (kernel x12-18, shared x9.5-10), so it does not change the exponent either.

Reading: pointer sharing is necessary, not sufficient. What it costs is in the key (an O(loose) walk per memoised node, and loose ranges here are 2n+), hashing, and the retained cells and values. The kernel gets its sharing for free from substitution that preserves pointers. Not tried: a cheaper key (hash-consed environments with an id, so the key is O(1)); that is the one variant that could close part of a factor of 8, and I would not expect it to beat the kernel. The NbE thread stays open: untried variants are an O(1) environment key, level-based terms, and instrumenting where the shared version's time goes (see the ranked list in the session notes below).

**n=64 (same replay, run later; CPU 86% busy at start, Defender RTP off, peak 2.81 GB under `memguard`):**

| n | hard queries | kernel | shared lazy | ratio |
|---|---|---|---|---|
| 32 | 285 | 0.83 s | 6.69 s | 8.1x |
| 64 | 573 | 7.89 s | 68.1 s | 8.6x |

All verdicts agree. The ratio has stopped falling (18x, 10x, 7.8x, 8.1x, 8.6x for n = 8 to 64), and growth per doubling is about 9.5x for the kernel and 10.2x for shared lazy, so the gap does not close with n; the early decline was fixed cost. A larger n does not rescue this design.

## 31. Where the shared lazy evaluator's time goes (counters and allocations)

`kernel_lazy::Stats` / `take_stats()` count the shared evaluator's lookups; a counting allocator (scratch, reverted) wrapped mimalloc to count allocations for both sides over the same replayed hard queries. Same exe, release, CPU 27% busy at start, Defender RTP off, peak under 8 GB under `memguard`.

| | n=16 | n=32 | n=64 |
|---|---|---|---|
| kernel `def_eq` time | 53 ms | 0.79 s | 8.4 s |
| kernel allocations (count / MB) | 0.55M / 37 | 6.0M / 409 | 75M / 5,150 |
| shared lazy time | 0.53 s | 6.5 s | 67.9 s |
| shared allocations (count / MB) | 2.6M / 317 | 19.9M / 2,605 | 156M / 22,997 |
| `eval` calls | 1.0M | 7.6M | 59.4M |
| keyed `eval` lookups, hit rate | 631k, 3.9% | 4.7M, 3.8% | 36.7M, 3.7% |
| keyed cell lookups, hit rate | 563k, 11.1% | 4.4M, 10.9% | 35.4M, 10.8% |
| average key length (slots) | 3.3 | 4.0 | 5.4 (393M slots over 72M keyed lookups) |
| memo entries at end (cells + vals + equal pairs) | 1.2M | 8.8M | 69.2M |
| conversion calls: pointer hit / pair-memo hit | 37% / 12% | 35% / 14% | 34% / 16% |

Reading:
- **The memo almost never hits** (4% of `eval` lookups, 11% of cell lookups) yet every miss inserts an entry. At n=64 that is 69M retained entries and 23 GB allocated, 4.5x the kernel's bytes and 2x its allocation count.
- **The amount of evaluation is not the problem.** 59M `eval` calls is the same order as the kernel's 75M allocations. Per operation the shared evaluator is about 10x slower (1.1 us per `eval` against about 0.1 us per kernel allocation), which matches the 8x time gap.
- **The few hits matter.** Without the memo the evaluator does not finish (§25), so the sharing is what turns an exponential into a polynomial. The cost is that it pays full price on the 96% that never repeat.
- **The walk is a minority cost, not the whole story.** Keys average 3-5 slots. An O(1) environment key removes that walk but not the insertions, retained entries, or the extra allocation per evaluation. I would expect it to close part of the gap, not most.
- **What this suggests.** The next variant worth trying is a memo that inserts selectively (for example only nodes whose measured hit rate is high, or a bounded cache), not a cheaper key. Which nodes hit is not yet measured: a histogram of hits and misses by key length or node size is the next cheap instrument.

## 32. Memoise closed nodes only: the shared lazy evaluator reaches the kernel's speed

Hit/miss histogram (n=32, 4.7M `eval` and 4.4M cell lookups) split by key length: nodes with **no loose variable** (key = just the address) are 4% of `eval` lookups and 9% of cell lookups, but hit 85% / 92% of the time and account for **93.5% of all `eval` hits and 75% of all cell hits**. Every node with a loose variable hits under 1% (`eval`) or 7% (cells, length 1) and is almost all of the traffic. By kind: `Lam` nodes give 92% of `eval` hits; `Var` cells are 79% of cell lookups and hit 3.4%. So the memo's cost is the 95% that never repeat.

Knob: `set_memo_max_loose(k)` memoises only nodes with at most `k` loose variables. Replay of the n=32 hard queries (same exe, back to back, machine idle at the first of these runs):

| memo limit | time | `eval` calls | memo entries |
|---|---|---|---|
| all nodes | 6.9 s | 7.6M | 8.8M |
| <= 2 loose | 3.0 s | 8.2M | 3.7M |
| <= 1 loose | 2.2 s | 8.3M | 2.6M |
| **closed only (0)** | **0.73 s** | 8.3M | 0.35M |
| kernel `def_eq` | 0.87 s | | |

Closed-only costs 9% more evaluation than the full memo and 20x less memory. It is now the default of `def_eq_lazy_shared`. Across n (CPU about 5% busy, Defender RTP off, peak memory 0.62 GB at n=32; kernel vs closed-only lazy, agreement with the kernel on every query):

| n | kernel | lazy, closed-only memo |
|---|---|---|
| 8 | 2.3 ms | 7.7-8.4 ms |
| 16 | 36 ms | 63-74 ms |
| 32 | 0.92 s | 0.50-0.55 s |
| 64 | 7.96 s | 6.3 s, 6.9 s, and one run of 63 s |

The 63 s run is an outlier that I did not diagnose (disk was at 100% when this batch started, with 23 GB freed just before; other sessions share the machine), so I report it rather than drop it. Kernel timings also moved between runs (n=16: 36 vs 76 ms).

Reading: the evaluator is now **level with the kernel from n=32 up (about 0.6-0.8x its time at n=32 and 64), and slower below that** (3.5x at n=8, 1.8x at n=16 from fixed setup). That is a constant-factor result, not a new exponent: lazy grew about 13x from n=32 to n=64 against the kernel's 8.7x on these runs, so on this evidence the lead is not guaranteed to widen. Allocation was not re-counted for the closed-only mode. As an untrusted evaluator it changes nothing in the kernel; putting it in the trusted checker would add about 400 lines of reduction code for a gain of this size, which I do not recommend on this evidence alone.

## 33. Literature check for the NbE thread (no code)

Sources read: RKNL abstract (arXiv 2603.21949, ICFP 2022); Coq 8.15.1 `kernel/reduction.ml` source (fetched raw, read `ccnv`/`eqappr`); our own §31 replay stats (`replay-stats.log`, full-memo mode).

- **Conversion subproblems are not the lever.** n=32 replay: 580k `conv` calls, 35% pointer-equal, 14% `equal`-memo hits, 51% real work, against 7.6M `eval` calls. Evaluation is 13x the conversion traffic, so hash-consing convertibility triples (option 2) can only touch the small side. Not pursued.
- **Coq shares across binders with lifts, not fresh variables.** `eqappr` head-reduces both sides lazily, and under a lambda recurses on the body with `el_lift lft1` / `el_lift lft2` over the same closures (`destFLambda mk_clos`), eta-expanding the other side. A shared closure keeps its identity under a binder and only a lift is adjusted. Our evaluator keys the memo by (address, relevant environment prefix), so a node with loose variables gets a new key each time the environment differs; that is the 95% that never repeats (§32). Whether a lift-style representation would make those keys repeat is untested. This is my reading of the source, not measured.
- **RKNL (strong call-by-need).** Abstract claims a number of steps linear in both beta-reductions and input size ("bilinear"). I could not read the body: the PDF text was not extractable here (no pdftoppm) and the fetch summaries disagreed with each other (one said O(n^2)), so the exact bound and the memothunk definition are **unverified**. Do not rely on either.

**Replay harness, now committed.** `--features record-defeq` makes `check_rc` log every `def_eq(inferred, expected)` with its context depth (`kernel::take_defeq_log`; compiled out by default, so the default kernel is unchanged), and `replay_defeq_queries` in `tests/church_bv.rs` replays the `add x 0 = x` lemma's queries through the kernel and `kernel_lazy` (command in its doc comment). It reproduces §31's counts (hard queries 69 / 141 / 285 at n=8 / 16 / 32; 8.33M `eval` calls at n=32 in closed-only mode). First run (CPU 41% busy, Defender RTP off, agree=true everywhere): n=8 kernel 3.7 ms vs lazy 14.9 ms; n=16 80 vs 129 ms; n=32 1.07 s vs 1.04 s. With the closed-only memo, `conv_equal_hits` is 84k of 593k `conv` calls at n=32, close to the full-memo replay's 83k of 580k.

**RKNL, from the arXiv HTML version (the PDF was unreadable here).** The abstract's claim stands: the machine simulates normal order in a number of steps linear in both the beta-reductions and the input size (Theorem 5.9, by amortised cost with a potential function). A memothunk is a mutable box holding either an unevaluated thunk or its value, so sharing comes from reaching the same box through the environment, not from a lookup table. Under a lambda the parameter is renamed to a fresh variable at a fresh store location, so one argument is evaluated and read back once however often it is used. The paper reports step counts for some term families, no wall-clock comparisons with other systems, and calls its contribution theoretical. This corrects the earlier "unverified" status of the bound; the fetch tool's earlier O(n^2) summary was wrong. Fit with us: our memo is a table keyed by (address, environment prefix), RKNL's is a box per argument. Whether boxes per argument would share what our keys miss is untested.

## 34. Option C (certificate-checking kernel): the premise fails (2026-09-30)

Idea C was: the untrusted lazy evaluator emits a hash-consed trace of reduction steps and the kernel checks the DAG, so cost follows DAG size, not tree size. First measurement, on the committed replay (`replay_defeq_queries`, CPU 34% busy, Defender RTP off, agree=true): beta steps taken on the lemma's hard queries.

| n | kernel betas | lazy betas | kernel time | lazy time (closed-only memo) |
|---|---|---|---|---|
| 8 | 724 | 54,155 | 3.8 ms | 13.3 ms |
| 16 | 1,964 | 374,099 | 79 ms | 96 ms |
| 32 | 5,980 | 2,792,675 | 1.07 s | 0.90 s |

(`record-defeq` now also exposes `kernel::take_beta_count`, counting `whnf_step`'s beta arm; `Stats::betas` counts closure applications of a `Lam`.)

Reading:
- **A lazy-evaluator trace is 467x larger than the kernel's own step count at n=32** (2.8M vs 6k betas) and grows faster (about 7.5x per doubling vs 3x). Certifying that trace would cost far more than the check it replaces. The lazy evaluator is level on time only because each of its steps is cheap.
- **The kernel's own trace is tiny (6k steps) but each step is a substitution.** 1.07 s / 5,980 betas is about 180 us per beta, and the hard queries' total tree size is 35.3M nodes (§26), so the kernel pays about 30 ns per tree node. A step-level certificate checker would still have to verify `body[arg] = result` for large bodies, which is the same substitution unless every traversal (hash-consing, `==`, `instantiate`, `nf`) is DAG-aware. Sharing at n=32 is about 11x (§26), so that bounds the gain; §20 already found pointer-memoised `instantiate` did not help.
- **Verdict:** C as stated is not worth building. The cost is term size per step, not step count, which points at A (keep carries shared in the statement so the terms are small) and B (prove once for all widths) instead.

## 35. Survey: lazier evaluation options, with pros and cons (2026-09-30)

What the kernel is today: `whnf_step` beta-reduces by eager `subst_top` (rebuilds every node on a path to a use of `Var(0)`, shifts the argument at each use, no pointer memo inside one substitution); `def_eq` reduces only where the sides differ, caches `whnf`/`nf` by pointer within one call; subterms with no loose variable are kept by pointer. `Const` is a postulate only (no definitions, no delta); `Free`/`Const`/`Var` already follow Lean/Isabelle's split (`2026-09-25-kernel-constants-and-loose-ranges-design.md`).

**Already tried here:** memoised `instantiate` (§20, lost); cache-retention skip (§23, lost); context overlay (§23-24, kept, about 25%); closure-based `kernel_lazy` (§25, 13-25x slower), with pointer-shared memo (§30-§32, parity with the kernel from n=32, same exponent); shrinking proof bodies (§26) and statement over `add_shared` (§28), no gain; step-certificate checking, option C (§34, dead: lazy trace 467x the kernel's steps).

**Literature (read as search summaries and two source files, not whole papers):**
- Lean 4 / Isabelle: locally nameless terms with a `let` binder and zeta-delta of let-variables; instantiate caches; a recent Lean PR makes `instantiateBetaRevRange` cheaper and increases sharing (so this is still being tuned there).
- Coq: `CClosure` lazy machine, lifts instead of fresh variables (§33).
- Explicit-substitution calculi (lambda-sigma, Accattoli's useful sharing): sharing stays polynomial without unfolding.
- smalltt (Kovacs): NbE with glued evaluation, unfolding of definitions controlled so conversion and readback share work.
- RKNL: memothunk box per argument, bilinear steps (§33).
- Hashing modulo alpha: with de Bruijn terms a structural hash is already alpha-invariant; re-hashing under binders is the cost in locally nameless form.

| Option | Pros | Cons | Fit with our measurements |
|---|---|---|---|
| **1. `Let` with lazy zeta-delta of let-variables** (state each carry once, `let c_i := carry(a_i, c_(i-1))`; conversion unfolds a let-variable only on demand and caches its whnf) | Attacks term size, the measured driver (§26, §34). Statement and inferred types stay O(n). Standard in Lean and Coq, soundness well understood | New `Expr` variant: touches `infer`, `shift`, `instantiate`, `whnf`, `def_eq`, the printer and every exhaustive match. Needs a rule for when conversion unfolds. §28 shows sharing in the statement alone does not survive beta, so the proof must use it too | Best match. The only option aimed at the 35M-node total |
| **2. Definitions + delta + lazy unfolding** (compare heads and arguments before unfolding, as Lean and Coq do) | Shared by name, never copied; classic congruence-first trick avoids reducing when heads agree | Closed definitions cannot mention the lemma's bit variables, so each carry becomes an application with O(i) arguments: no size gain for this lemma. Needs delta in `Globals` and an unfolding heuristic | Weaker than 1 here; better for reusable library functions |
| **3. Explicit substitution nodes in `Expr`** (lambda-sigma, beta builds a substitution node, forced by `whnf`) | No body rebuilt, polynomial without unfolding sharing | Largest kernel change; new term forms everywhere; shift/lift algebra to audit; lands close to the L2 rewrite | Our own L1 shows the cost: 467x more steps, offset only by cheap steps |
| **4. Locally nameless instantiate** (open binders with fresh `Free`, no shifts, closed arguments) | Removes `shift` (3.4M calls at n=32 in §19); makes a pointer memo of `instantiate` sound across depth | Rewrite of binder handling in `infer`/`check`/`conv`; the kernel already has `Free` and abstraction on exit, so part exists | §20 says memoised instantiate alone lost; this removes its depth key but not the tree walk |
| **5. Structural hash per node (cached, like `loose`)** | Cheap early reject in `==`; lets caches hit on equal copies (the kernel doc says a copy misses the pointer cache); union equal pointers after a successful `==` | Extra word per node and compute on every allocation, in a kernel whose cost is allocation and teardown (§20-§22) | Cheap to probe: count whnf-cache misses on structurally equal terms |
| **6. Bidirectional spine checking** (check arguments against domains without building the large instantiated codomain) | Aims at the "large inferred vs small expected" shape directly | Not a conversion change; codomain still has to be instantiated to check later arguments; unproven that it avoids the big term | Speculative |
| **7. Native/VM reflection** (Coq `vm_compute`, Lean `decide +kernel`; the repo has a wasm JIT) | Fast on closed computation | Trusted base grows; does not help the symbolic lemma | Different problem |
| **8. RKNL / useful sharing in the untrusted evaluator** | Bilinear steps in theory; fewer steps than our memo | Untrusted only; the evaluator is already level with the kernel, so a faster one still has no trusted use | Research value only |
| **9. Induction over width (B)** | Removes the n dependence rather than speeding it up | Needs a computing `Bool`/`Nat` (§11) | Orthogonal; see next-step list |

**Novel in this setting (mine, untested):**
- **Context let-variables with a per-variable whnf cache** is option 1 stated precisely: the sharing lives in one context entry, so every mention is O(1) and its normal form is computed once for the whole check.
- **Equality classes for successful `==`**: the kernel remembers only unequal pairs (`eq_noting`); after a successful walk it could union the two pointers so later compares are O(1). Only 14% of lazy `conv` calls were `equal` hits (§33), so expect a small gain.
- **Generator-side compression**: have the Rust lemma generator emit each carry once and reference it through a let-bound abstraction `(\c_i. rest) e`, then measure whether conversion's beta undoes it (§28 says yes), which is the case for option 1.

## 36. Two probes from the §35 survey (2026-09-30)

Both on the lemma's hard queries (`probe_hard_queries`, `--features record-defeq`; since removed from the tree, in history at `c156cef`; CPU 51% busy, Defender RTP off, free memory 32 GB; times are with the probe's own hashing, so only the counts matter). `tree_total` is the summed tree size of the two compared terms per query, `dag_total` the distinct nodes per query summed.

| statement | n | hard | tree_total | dag_total | tree/dag | betas |
|---|---|---|---|---|---|---|
| `add` | 8 | 69 | 612k | 125k | 4.9 | 724 |
| `add` | 16 | 141 | 4.61M | 591k | 7.8 | 1,964 |
| `add` | 32 | 285 | 35.3M | 3.08M | 11.5 | 5,980 |
| `add_shared` | 8 | 69 | 602k | 126k | 4.8 | 731 |
| `add_shared` | 16 | 141 | 4.56M | 594k | 7.7 | 1,979 |
| `add_shared` | 32 | 285 | 35.1M | 3.08M | 11.4 | 6,011 |

**Probe 1, carries let-bound by the generator (`add_shared` statement): no change** (35.1M vs 35.3M at n=32, max term 492k in both). Same result as §28 and for the same reason: the inferred types come from the proof's own terms, which still mention each carry inline, and conversion beta-reduces `(\c. rest) e`. This rules out a generator-only version of option 1. It does **not** test a kernel `Let` with lazy unfolding, where the proof body and the inferred types would also carry the shared name. Inconclusive for that.

**Side finding, not what the probe was for:** DAG size grows about 4.7x then 5.2x per doubling (roughly n^2.3), tree size 7.5x then 7.7x (roughly n^2.9), so the tree/dag ratio widens with n (4.9, 7.8, 11.5). A traversal that costs by distinct node, not tree node, would have a lower exponent, not just a constant. Our lazy evaluator did not realise that: its `eval` calls grew 7.0x and 7.5x (158k, 1.11M, 8.33M), like the tree.

**Probe 2, content-keyed `whnf` cache** (hash each missed node structurally, within one `def_eq` call, count misses whose structure was already missed at a different address). The hash is 64 bits, so duplicates are counted with a tiny false-positive chance:

| n | whnf misses | duplicate by structure | tree nodes over misses | over duplicates |
|---|---|---|---|---|
| 8 | 858 | 300 (35%) | 1.04M | 164k (16%) |
| 16 | 2,210 | 936 (42%) | 9.39M | 2.20M (23%) |
| 32 | 6,450 | 3,168 (49%) | 102M | 32.4M (32%) |

About half the cache misses at n=32 are for a term the cache already holds under another address, and the share rises with n. So hash-consing (or a content-keyed `whnf` cache) is an upper bound of roughly 2x on the `whnf` count, by size weight less (32%), and it costs a hash per allocation in a kernel dominated by allocation and teardown (§20-§22). Not a clear win, but the first measured lead that grows with n.

## 37. Where the DAG-sized work is lost: it is `instantiate`, and not through missed sharing (2026-09-30)

Node visits per kernel function on the lemma's hard queries (`walk_counts_on_hard_queries`, `--features record-defeq`; CPU 41% busy, Defender RTP off; the run with hashing probes on is 8-12x slower, so only counts are quoted):

| n | time (no hash probes) | betas | `instantiate` visits | `shift` | `==` (`eq_noting`) | `conv_whnf` |
|---|---|---|---|---|---|---|
| 8 | 5.0 ms | 724 | 50,811 | 11,438 | 27,808 | 141 |
| 16 | 75 ms | 1,964 | 476,087 | 74,734 | 123,696 | 277 |
| 32 | 954 ms | 5,980 | 5,444,527 | 521,070 | 678,608 | 549 |

- **`instantiate` is 82% of all node visits at n=32 and, at about 175 ns a visit, accounts for essentially the whole 0.95 s.** `shift` and `==` are each about a tenth of it. `conv_whnf` calls are only 549: the comparison itself is cheap.
- **Its growth is about n^3.2-3.5** (visits x9.4, x11.4 per doubling) = betas (x2.7, x3.0) times visits per beta (70, 242, 910; x3.5, x3.8, about n^1.9). Each beta substitutes into a body of about 900 distinct loose-bearing nodes at n=32.
- **No DAG waste inside one substitution.** Distinct (node, depth) pairs per `subst_top` call are 99.9% of the visits (5,438,914 of 5,444,527 at n=32). A pointer memo inside `instantiate`, like §20's, has nothing to skip: this is the measurement behind why it lost.
- **Across substitutions there is repetition, bounded at about 2x.** Counting by structure (body and argument hashed), 72% of the 5,980 betas at n=32 substituted a (body, argument) pair already substituted earlier (52% at n=8, 63% at n=16), carrying 27%, 38% and 50% of the `instantiate` visits (13.9k of 50.8k, 180k of 476k, 2.71M of 5.44M). A content-keyed beta cache would remove up to that share, so at most about 2x at n=32, rising with n. The visits that are not repeats still grow x8.0 then x9.2 per doubling, so the exponent stays near 3. This matches the content-keyed `whnf` cache bound in §36 (49% of misses duplicate), and is the same repetition seen from the substitution side.
- **Reading.** The kernel is not missing DAG sharing in its traversals. The n^3 is the product of the number of betas (n^1.5) and the distinct loose-bearing nodes in each body (n^1.9). Anything that changes the exponent must shrink what a beta rebuilds: lazy substitution (environments, which the lazy evaluator does at the price of 467x more steps) or keeping the carry chain out of the bodies (kernel `Let`, untested). A content cache is a constant factor of at most 2x.

The hashing probes (§36 `struct_probe`, this section's distinct-visit and beta-pair counters) are in the history at the commit that added this section and are removed in the next one; the plain counters (`take_walk_counts`, `take_beta_count`) stay behind `record-defeq`.

## 38. Suspension calculus: what the papers say (2026-09-30)

Read via the ar5iv HTML of arXiv cs/0702152 (Nadathur et al., "A Simplified Suspension Calculus and its Relationship to Other Explicit Substitution Calculi") and cs/0404020 ("A treatment of higher-order features in logic programming", the lambda Prolog / Teyjus paper). Rules and figures below were each fetched twice with different prompts and agree; the PDF versions were unreadable through the fetch tool.

**Syntax.** A suspension is `[[t, ol, nl, e]]`: term `t`, `ol` = abstractions enclosing it before the beta contraction, `nl` = abstractions remaining after it, `e` = environment of `(term, level)` pairs. Beta is one rule that substitutes nothing: `((λ t1) t2) -> [[t1, 1, 0, (t2, 0)::nil]]`.

**Rules (verbatim shapes).** Reading rules push a suspension inward: constants (r1), index with empty environment is renumbered `#i -> #(i+nl)` (r2), the first index takes the environment's term `[[#1,ol,nl,(t,l)::e]] -> [[t,0,nl-l,nil]]` (r3), other indices decrement (r4), distribute over application (r5), and under a binder extend the environment with `(#1, nl+1)` and raise both levels (r6). Merging rule m1 composes a suspension inside a suspension into one with `ol' = ol1+(ol2-nl1)`, `nl' = nl2+(nl1-ol2)` and a composite environment, so two walks become one.

**Results (paper 1).** Reading and merging rules terminate (Thm 3.6, formally verified in Coq); they are confluent (Thm 3.12) and the full system with `beta_s` is confluent even with metavariables (Thm 3.18); it simulates beta soundly and completely (Thm 3.20, 3.21). It relates itself to lambda-sigma and other calculi. **No experiments.**

**Measurements (paper 2, in the lambda Prolog setting).** "Using the suspension notation and the rules (beta_s') and (r8) judiciously can reduce substitution walks to between a third and an eighth of what is needed when substitutions are performed eagerly" (section 4.2); computation time down "up to 35%" overall in some important cases; a dependence annotation on terms gives a speedup "over 70% in several cases" over eager propagation (section 4.3). The text names no benchmark programs, so the numbers are unattributed to a workload; empirical details are deferred to other papers.

**What this means here.**
- The merged walk (m1) is the one real novelty over our `instantiate` + `shift`: a substitution under a binder combines its shift and its replacement in one traversal, which our `instantiate` partly does already (it shifts `s` only where `Var(d)` is used, §50-§58 in RELATED_WORK).
- **The "dependence annotation" is our cached `loose()` range.** The kernel already skips every subterm with no variable at or above the current depth, so the 70% figure describes a gain we have mostly taken.
- The walk-reduction claim (a third to an eighth) is for lambda Prolog's unification-heavy terms with no stated benchmark. Our §37 measured the walks directly: 5.44M `instantiate` visits at n=32, with 99.9% distinct within each call, so the savings would have to come from not walking bodies that a later reduction discards, which is untested for our workload.
- None of this is evidence that suspensions beat eager `instantiate` on the Church-tuple lemma. It supports the mechanism, not the size of the gain.

## 39. The explicit-substitution families, with search-backed facts (2026-09-30)

Facts below come from search-result summaries of the papers' abstracts and listings (not the full texts), except §38's suspension rules, which were read. They replace the memory-based table given earlier in the session. One claim from the search summaries is dropped: that open-term confluence and strong-normalisation preservation cannot coexist. A paper in the same results is titled "extending a lambda calculus with explicit substitution which preserves strong normalisation into a confluent calculus on open terms", so a calculus with both is claimed to exist.

| Family | Established properties (source) | Pros | Cons | Fit for the kernel |
|---|---|---|---|---|
| **lambda-sigma** (Abadi, Cardelli, Curien, Levy) | Not confluent on all terms, confluent on ground terms only (Curien-Hardin-Levy abstract). I could not confirm the strong-normalisation counterexample attributed to Mellies from these results | First-class substitutions with composition; the base for later calculi | Open-term non-confluence; many rules | Weak: conversion goes under binders, i.e. through open terms, so we would have to lean on a fixed strategy and prove it simulates beta |
| **lambda-sigma-up** (Curien, Hardin, Levy) | Adds a lift operator and obtains a confluent calculus on open terms | Fixes open-term confluence | Still the large rule set of lambda-sigma | Same audit-size objection |
| **lambda-upsilon** (Benaissa, Briaud, Lescanne, Rouyer-Degli, JFP 1996) | Simple; implements beta correctly; confluent on closed terms; preserves strong normalisation of beta | Fewest rules; the SN property that lambda-sigma lacks; de Bruijn based | Open-term confluence only in an extension | Best minimal-rule candidate |
| **lambda-es** (Kesner, LMCS 2009) | Full composition, simulation of one-step beta, preservation of beta-SN, SN of typed terms, confluence on metaterms (abstract) | The strongest property list of the group | Stated in named-variable notation, not de Bruijn; our kernel is de Bruijn | Useful as a reference for what is provable, harder to adopt |
| **Suspension calculus** (Nadathur et al.) | Reading and merging rules terminate (checked in Coq), confluent with metavariables, simulates beta soundly and completely (§38) | Built for implementation; merged shift-and-substitute walk (m1); de Bruijn terms are the suspension-free subset; mechanised termination | Two level counters per suspension; designed for lambda Prolog unification; reported savings (a third to an eighth of the walks, up to 35% time) come from unnamed workloads | Best documented match to `instantiate` + `shift` |
| **lambda-sigma-w-a** (Benaissa, Lescanne, Rose, BRICS 1996) | Sharing, explicit recursion, space leaks and parallel evaluation modelled for weak reduction strategies | Describes environment-based vs graph-reduction implementations precisely | Weak reduction only | Matches the lazy evaluator, not a strong-reduction checker |
| **Useful sharing** (Accattoli, Dal Lago) | Strong call-by-name machine with quadratic overhead in the number of beta steps (2014); strong call-by-value with linear overhead (later work); RKNL for call-by-need is bilinear (§33) | Cost model proved reasonable; avoids steps that only unshare the output | Machine-level results, not a small trusted rule set | Research value; hard to audit |
| **Environment machines** (Coq `CClosure`) | Lazy reduction with sharing since 1996 (Barras); let-reduction added 2000 | Production precedent, handles binders with lifts | Machine state, so adopting it is the whole-checker rewrite (L2) | The proven route, the largest change |

**Updated ranking for this kernel:** suspension calculus first (mechanised termination, de Bruijn native, targets our `instantiate` + `shift` pair), lambda-upsilon second (smallest rule set), environment machine third (proven but a rewrite). Strong-normalisation preservation is the property to check before adopting any of them: if the substitution rules can loop on a term beta normalises, the checker hangs where it should answer (a completeness and denial-of-service problem, not unsoundness). Lambda-upsilon is claimed to preserve it; for the suspension calculus the sources above show termination of the reading and merging rules and beta simulation, not preservation of beta strong normalisation, so that point is open for it.

## 40. Suspension calculus and strong normalisation; how many betas are chained (2026-09-30)

**Does the suspension calculus preserve beta strong normalisation? Open, but conjectured.** Search results from the suspension-calculus papers (Nadathur and Wilson, TCS 1998; cs/0702027): preservation of strong normalisation for the suspension calculus "remains open"; the authors conjecture it holds and argue that the known lambda-sigma counterexamples do not carry over. Melliès's counterexample (beta-strongly-normalising terms that stop being so once substitutions are explicit) does not apply because rule (m6), the counterpart of lambda-sigma's `Map`, distributes only the relevant part of an external environment over substitution terms. The lambda-sigma failure is described as beta and the substitution rules interacting so a substitution scopes over its own subcomponents. Also named in the results: lambda-d and lambda-dn, calculi with (weak) composition that preserve beta strong normalisation. Source: search summaries, not the full texts.

**Kernel counters for the chained-beta question** (`walk_counts_on_hard_queries`, `--features record-defeq`; CPU about 40% busy, Defender RTP off; all counts are of the hard queries):

| n | betas | betas whose function was produced by a beta | `instantiate` visits spent producing that lambda (upper bound) | of all visits | betas whose lambda body is itself a lambda | their visits |
|---|---|---|---|---|---|---|
| 8 | 724 | 471 (65%) | 31,866 | 50,811 | 582 | 38,189 |
| 16 | 1,964 | 1,447 (74%) | 336,710 | 476,087 | 1,686 | 386,625 |
| 32 | 5,980 | 4,935 (83%) | 4,351,326 (80%) | 5,444,527 | 5,430 (91%) | 4,763,241 (87%) |

- **Most betas hand a lambda straight to the next beta.** At n=32, 83% of betas consume a lambda that another beta had just produced, and 91% substitute into a body that is itself a lambda (nested lambdas such as `\a. \b. \c. ...`). Those betas carry 87% of the `instantiate` visits.
- **Upper bound on what a one-pass multi-argument substitution could save:** the 80% of visits spent on lambdas that are applied at once, because each such pass rebuilds the whole remaining body only for the next beta to rebuild it again. The single fused pass still costs about one pass over the innermost body, so the realistic saving is less than 80%; this is a bound from counters, not a measured speedup.
- **Chain lengths:** non-chained betas (chain roots) are 253, 517 and 1,045 at n=8, 16, 32 (about x2 per doubling, so about n^1), against 724, 1,964 and 5,980 betas in total: the mean chain is about 2.9, 3.8 and 5.7 betas long and growing with n.
- **Reading.** This is the cheapest lead so far: a kernel-local change (peel nested lambdas on an application spine and substitute all available arguments in one `instantiate` pass, as Lean's `betaRev` does from memory) aimed at the exact cost §37 found. It does not need suspensions. Untested; needs a go-ahead because it edits `whnf_step`.

The counters (`take_chain_counts`, `take_direct_counts`) stay behind `record-defeq`. The chain count includes every beta inside the head reduction, so the visit figure is an upper bound.

## 41. One-pass multi-argument beta in the kernel (2026-09-30)

- **Change.** `instantiate` is now a wrapper over `instantiate_n(e, args, d)`, which discharges `args.len()` binders in one walk. `whnf_step` tries `beta_spine` first on any application whose function is itself an application: it collects the spine, reduces the head, peels as many directly nested lambdas as there are arguments, substitutes them all at once, and applies any leftover arguments. A stuck head returns `None`, so the one-argument path and its per-prefix cache entries run unchanged.
- **Check.** New test `instantiate_n_matches_sequential_substitution` (20,000 random terms, 1 to 3 arguments, against `instantiate_ref` applied one argument at a time). Lib tests: 352 pass (kernel: 104). `church_bv`: pass. Replay: all verdicts agree at n=8/16/32.
- **Result (n=8/16/32, Defender state and machine load not recorded for this run).**

| | before | after |
|---|---|---|
| kernel betas | 724 / 1,964 / 5,980 | unchanged (counted per argument) |
| `instantiate` visits | 50.8k / 476k / 5.44M | 13.3k / 89.8k / 677k |
| kernel replay time | n=32 about 0.95 to 1.04 s | 176 ms (walk-count run: 284 ms) |

- **Exponent.** Visits grow 6.7x then 7.5x per doubling, so about n^2.75 to n^2.9, down from n^3.2 to n^3.5. Part of the win is the constant (8x fewer visits at n=32), part is the exponent; the exponent is still above n^2.5, so the chains do not account for all of the growth.
- **Not yet done.** The chain and direct-lambda counters now read 0 because the spine path bypasses them. n=64 has not been timed. The two-argument-at-a-time case where the head is not a lambda until after one beta (`(\x. \y. b) a` reduces to a lambda and the next argument arrives through a different spine) is not fused.

## 42. After the fusion: n=64 and n=128, and what still scales (2026-09-30)

- **Conditions.** Defender real-time protection off; CPU 24 to 30% busy (another session's `manifold` render loop was running), so timings are noisy. Two runs of the full lemma check (generation plus typecheck, `add_zero_lemma_scaling`, now n up to 128):

| n | run 1 | run 2 |
|---|---|---|
| 8 | 34 ms | 82 ms |
| 16 | 187 ms | 456 ms |
| 32 | 1.19 s | 2.69 s |
| 64 | 9.2 s | 17.2 s |
| 128 | 123 s | 65.7 s |

  Best of two: 5.6x, 6.4x, 7.7x, 7.1x per doubling, so about n^2.5 to n^2.9. The earlier 63 s outlier at n=64 did not recur (9 to 17 s), which points to contention rather than a kernel effect; not proven.
- **Walk counts on the hard queries** (kernel only, quiet-ish run): `instantiate` visits 13.3k / 89.8k / 677k / 5.31M, shift 9.4k / 65.7k / 483k / 3.68M, eq 27.8k / 124k / 679k / 4.39M. Betas 724 / 1,964 / 5,980 / 20,156 (about n^1.75).
- **Correction to §41.** The n=32 to n=64 step is 7.85x for `instantiate` (n^2.97) and 7.6x for shift, so the visit exponent is still about 3, not 2.75 to 2.9. Fusion cut the constant (8x at n=32), not the growth. Per-beta cost still grows about n^1.2: the number of betas is sub-quadratic but each one walks a body whose size grows with n.
- **Reading.** Shift is 70% as large as `instantiate` and shares its growth: arguments are copied under binders at each use. That is the target `Let` or a shared-argument scheme would hit, not further fusion.

- **Counters removed.** The chain and direct-lambda counters (§40) are deleted; they had read 0 since the spine path bypassed them and had answered their question. `take_beta_count` and the walk counts remain behind `record-defeq`.

## 43. Probe: where `shift` visits come from (2026-09-30)

- **Counter.** In `instantiate_n`'s `Var` case (a substituted use), classify each use by binder depth `d` and whether the argument has loose variables, and attribute the `shift` visits it costs. Behind `record-defeq` (walk slots 5 to 9; `PROBE` lines in `walk_counts_on_hard_queries`).
- **Result.** At n=8/16/32/64, uses of a substituted argument: 835 / 2,435 / 7,939 / 28,163. Of those, at depth 0 (no shift needed): 315 / 715 / 1,899 / 5,803; deeper with a closed argument (free ride): 39 / 71 / 135 / 263; deeper with loose variables: 481 / 1,649 / 5,905 / 22,097. **All** `shift` visits (9.4k / 65.7k / 483k / 3.68M) come from that last class, which is 78% of uses at n=64.
- **Growth.** Shift visits per such use: 19.6 / 39.9 / 81.8 / 166.6, so each shifted argument grows linearly with n; uses grow about n^1.4.
- **What it does not show.** A loose variable in an argument may be a reference to the checker's context (which `Free` instantiation would remove) or to a binder inside the term being reduced (which it would not). The probe cannot tell them apart. Shift is 41% of all walk visits (3.68M of 8.99M at n=64), so at best removing it all saves that fraction, and the 5.3M `instantiate` visits remain.

## 44. Probe 2: the loose variables in shifted arguments are the checker's context (2026-09-30)

- **Counter.** `conv_whnf` tracks how many binders the comparison has opened (it compares binder bodies in place, without instantiating them); each deeper-loose use in `instantiate_n` is then classed internal (the argument mentions one of those binders, tested with `is_var_free` on indices below the depth) or context-only. Behind `record-defeq` (walk slots 10 to 14; `PROBE2` line). Assumes binder children are `Pi`/`Lam`/`W`/`Sigma` second field, `Pair`'s `fam`, `WRec`'s `children_ty`; other shapes are not tracked.
- **Result.** At n=8/16/32/64 every deeper-loose use is context-only: 481 / 1,649 / 5,905 / 22,097 uses and all 9.4k / 65.7k / 483k / 3.68M shift visits, none internal. The probe is live: `conv` opened 67 binders at n=8 and 515 at n=64.
- **Reading.** The arguments are shifted because they mention the lemma's own context variables, which instantiating them with `Free` at binder entry would make closed and so skip `shift`. This clears the precondition for option C (§42, pros and cons); it does not show the net win, since entering a binder then costs an instantiate of the body and an abstraction on the way out, and `instantiate`'s 5.3M visits are untouched.
- **Caveat.** The 515 opened binders are a small share of the 1,093 `conv_whnf` calls, so "no internal" partly reflects that the hard queries mostly compare context-level terms. A workload that reduces under many binders could differ.

## 45. Option C estimated: renaming the context to `Free`s costs more than it saves (2026-09-30)

- **What I read.** The checker (`infer_node`, `check_rc`) works in de Bruijn indices with a per-binder `CtxScope` and caches keyed by (pointer, context id); it rejects any `Free` outright (`free_escaped`, `free_of`), which is a soundness invariant: `Free` is a builder-side parameter (`Scope::bind`, `abstract_frees`). So the invasive form of option C (instantiate each entered binder with a `Free`) would turn that invariant inside out, add an instantiate per binder entry (depth times body size, against a checker that enters binders for free today), and an abstraction on exit. Not attempted.
- **A cheaper form, measured.** At each hard query, rename the context variables in both sides to `Free(0..depth)` in one pass (`rename_context_to_frees`, `rename_pair_memo`; the comparison is unchanged because the renaming is injective and the terms contain no `Free`), then run `def_eq`. Probe only, in `walk_counts_on_hard_queries` (`RENAME` lines).
- **Result (n=8/16/32/64).** After renaming, `def_eq` does no shifts and few instantiates: instantiate visits 2.9k / 8.3k / 25.9k / 88.9k (plain 13.3k / 89.8k / 677k / 5.31M), shift 0 (plain 9.4k / 65.7k / 483k / 3.68M); `def_eq` itself 1.4 / 6.2 / 36 / 209 ms. But the renaming pass visits 33.9k / 262k / 2.04M / 16.0M nodes unmemoised, or 27.8k / 205k / 1.54M / 11.9M with a pointer-keyed memo (5.3 s at n=64 with the hash map, noisy machine). That exceeds the 9.0M visits it removes at n=64. Whole-term renaming is a net loss; the plain evaluator only touches the parts of the terms it needs.
- **Per-query shift memo, measured.** Distinct (argument, depth) shifts within one `def_eq` are 411 / 1,378 / 4,851 / 17,939 of 481 / 1,649 / 5,905 / 22,097, and cost 94% to 99% of the shift visits (3.64M of 3.68M at n=64). Memoising shifts per query would save about 1%. Dead.
- **What is left.** The win is real only if the renaming were lazy: rename a context variable where `whnf` looks at it, not up front. That is a different term representation for context variables (an environment, or de Bruijn levels for the context and indices only for internal binders), not a cheap patch. Both touch every `Var` case in the trusted core. Option A (`Let`) remains the other route; this probe gives it no new support or opposition.
- **Method notes.** Pointer identity in the memo probe can alias if a node is freed and its address reused within one `def_eq`; the effect would be to overstate duplicates, and the result is "almost none", so it stands. Machine load was elevated during the timings (another session's job); visit counts are unaffected.

## 46. Option 2 surveyed deeper: binder representation and shifts, plus a correction to the target (2026-09-30)

**Correction first (shift column corrected in §47: the first run also counted the proof generator's shifts).** Every probe in §37 to §45 measured only the hard `def_eq` queries (the ones where the two sides differ). Walk counts for the *whole* lemma check (`CHECK ... whole-check visits` in `walk_counts_on_hard_queries`, includes the `==` fast path and all of `infer`):

| n | instantiate | shift | eq | hard-query share of instantiate / shift / eq |
|---|---|---|---|---|
| 32 | 2.83M | 2.10M | 6.79M | 24% / 23% / 10% |
| 64 | 18.06M | 14.87M | 50.83M | 29% / 25% / 9% |

At n=64 the hard queries are 29%, 15% and 9% of those visits; the exponent of each whole-check column is about 2.7 to 3 (n=32 to 64: 6.4x instantiate, 7.1x shift, 7.5x eq). Shift visits in `ctx_lookup` (a stored type shifted by k+1 per `Var` use): 0.55M / 3.63M, 24% of the whole-check shift at n=64. The rest of the shift and instantiate work, and most of `eq` (46M of 50.8M at n=64, from `==` on queries that turn out equal), is in `infer`, which the fusion of §41 did not touch. Wall time agrees in direction (whole check about 10x the hard-query replay at n=32 under the feature, which also logs every query, so the ratio is inflated), but the machine was at 80 to 98% CPU for these runs, so only the visit counts are reliable. The earlier claims that `instantiate` is "essentially the whole time" hold for the replay, not for the check.

**Binder representations, as applied to the shifts we measured.**

1. *Locally nameless in the checker (Lean).* Entering a binder substitutes a fresh `fvar` into the body; nested binders are batched (one `instantiate_rev` over a buffer of fvars, then one abstraction to rebuild the type). Arguments are closed, so no shifts. The Lean kernel arena's `perf/shift-cascade` (1,000 nested lets) is reported as linear for locally nameless kernels and quadratic for a de Bruijn kernel with deferred `Shift` wrappers. Cost for us: an instantiate of the body per binder group and an abstraction on exit; §45 measured the closest cheap form (rename everything up front) as a net loss, and our checker deliberately rejects `Free`.
2. *Pure de Bruijn with lazy shifts (nanobruijn, an experimental Rust Lean kernel forked from nanoda).* Each pointer carries an integer offset, so a shift is O(1) and terms differing by a uniform shift share a node; the cache is bucketed by binding depth (a result at one depth is reused at another by adjusting the offset, closed terms live in a global bucket); and a frame's cache is kept on leaving a binder if the next binder has the same type. Reported on the arena against the locally nameless baseline: Mathlib 13.2 min (2.4x faster), Init 37.2 s (-44%), Cedar -45%, but con-leche +5.1x memory. This is the closest published match to our measured cost (shifts of context-only arguments), and it is a Rust kernel.
3. *Environment machines with levels for free variables (smalltt; NbE).* Closures and de Bruijn levels, indices only in quoted output; no shifting at lookup. Our own `kernel_lazy.rs` is the closure form and was only a constant factor (§32), so this is the least promising for a fixed exponent.
4. *Coq's `esubst` lifts / explicit-substitution shifts (§35, §39).* Shifts are deferred in the environment (`ELSHFT`), same family as option 2's lazy shift but inside closures.

**What each would change here.**
- *Lazy shift as a node (`Lift(e, cutoff, k)`).* Needs a new `Expr` case in every traversal and a rule that exposing a head pushes the shift one layer in (`Lift(Lam(a,b),c,k)` to `Lam(Lift(a,c,k), Lift(b,c+1,k))`); `==` on two `Lift` nodes with the same cutoff and shift can compare the sources. The measured shift (14.9M at n=64 whole-check) is the ceiling, and §45 showed a per-query shift memo helps only 1%, so the gain depends on how little of each shifted argument is ever examined. Unmeasured; that is the probe to run first.
- *Context types stored pre-shifted or by level.* `ctx_lookup`'s shift is 24% of the whole-check shift; storing each type at its lookup depth would not avoid it, but a (pointer, k) memo or levels would. Smaller target, smaller change.
- *The `eq` walk.* 46M of 50.8M visits at n=64 are `==` on equal sides that are not pointer-equal. Hash-consing or a shared-structure shortcut targets the largest single number, independent of the binder representation. Not measured beyond the count.

**Sources (summaries fetched through a small model; the arena figures and design notes were not checked against run logs or source).** Lean Kernel Arena pages for nanobruijn and `perf/shift-cascade`; Lean4Lean (arXiv 2403.14064) for the Lean kernel's `infer_lambda` with batched `instantiate_rev`; smalltt README for levels and closures; Charguéraud, locally nameless with cofinite quantification, for the representation itself.

## 47. Where the whole check spends its time: infer's caches, not the hard queries (2026-09-30)

- **Visit counts by call site, whole check, n=32 / n=64** (`SITES` lines; `[instantiate, shift, eq]`): `def_eq` 677k / 5.31M, 483k / 3.68M, 6.79M / 50.8M; `ctx_lookup` shift 547k / 3.63M; `App` rule's `subst_top` 1.47M / 7.39M instantiate and 241k / 975k shift; everything else (the other `infer` arms) 685k / 5.36M instantiate and 827k / 6.58M shift. So outside `def_eq`, `infer`'s `App` rule is the largest `instantiate` source (41% of the whole check at n=64) and the other arms the largest `shift` source (44%). Whole-check totals: instantiate 18.06M, shift 14.87M, eq 50.83M. (An earlier version of this section's table counted the proof generator's shifts too; fixed in §46.)
- **The `eq` walk is many tiny queries.** At n=8/16/32/64 the easy (equal) queries are 35.8k / 194k / 1.17M / 7.84M. At n=64, 3.05M take 1 to 3 visits, 4.79M take 4 to 15 (33.5M visits, about 7 each), 149 take 16 to 63, and 805 take 64 or more (3.71M visits, about 4.6k each). Query count grows 5.4x, 6.0x, 6.7x per doubling. Hash-consing or pointer sharing would help only the 805 large ones (7% of `eq`); the rest is the number of queries, one per `check_rc` node of a proof that is itself about n^2.6 in size.
- **Profile (samply, n=64, whole check, no feature, machine at about 70% CPU from other jobs, so read proportions only; 19.5k samples).** Inclusive: `check_rc`/`infer` 88%; `def_eq` 15%; `whnf` 16%; `instantiate_n` 11.7%; `shift` 10.9%; `InferCache::enter` 8.5%; `HashMap` find 10.3% and insert 4.4%; `drop_glue` 14% (of which `drop_inner_table` 6.8%); `foldhash::gen_per_hasher_seed` 4.6%; `Rc::new` 10.6%; `mi_malloc` 5.2%. Top self time: `infer_rc` 15% (hash lookup keyed by (pointer, context id)), `InferCache::enter` 5.5%, `same_shape` 4.9%, `gen_per_hasher_seed` 4.3%. Reading: the infer memo (pointer-keyed map, per-context ids, tables built and dropped) and hasher setup cost roughly as much as the whole `def_eq` machinery that §37 to §45 worked on. `gen_per_hasher_seed` being visible suggests many short-lived `HashMap`s (one `ReductionCache` per `def_eq` call, 7.8M calls at n=64), each seeding its hasher; a fixed hasher for these pointer-keyed maps, or building the cache lazily after the `==` check, would remove it. Not tried.
- **Consequence.** The campaign so far (fusion, probes, §45) improved only the 15% `def_eq` share. The remaining large shares are the `infer` cache bookkeeping (about 25 to 30% by the figures above, overlapping), allocation and drop (about 14%), and `infer`'s own substitutions. The next measurement is a profile with the infer cache and per-call caches broken out, then fix the cheapest.
- **Probes kept.** Behind `record-defeq`: `SITES`, `EASY`, `CHECK` lines in `walk_counts_on_hard_queries`; `profile_add_zero_n64` (ignored test, no feature) for samply runs.

## 48. Fixed hasher for the reduction and infer caches; infer memo statistics; the new split (2026-09-30)

- **Change (trusted file, performance only).** `ReductionCache` and `InferCache` use `PtrMap`/`PtrSet`: hashbrown maps with a seedless multiply-and-rotate `PtrHasher` instead of the default randomly seeded hasher. A `ReductionCache` is built for every `def_eq` call (7.8M at n=64, nearly all ending at `==`), and seeding its three hashers was 4.3% of the whole check (§47); the keys are the checker's own pointers and ids, so a random seed defends nothing. Also moved `whnf_step`'s doc comment back above `whnf_step` (my `beta_spine` insertion had split it). All 352 lib tests and the integration tests pass.
- **Effect.** Interleaved A/B of the two binaries on a machine at 63 to 86% CPU from other jobs (`whole_check_time`, best of 3 per width, three alternations): new was at or below baseline in all six pairs. Best seen: n=32 1.32 s vs 1.48 s (-11%), n=64 9.26 s vs 11.9 s (-22%). Run-to-run noise on this machine is 2x, so treat the size as 5 to 20%, the sign as likely. `foldhash::gen_per_hasher_seed` is gone from the profile, which had 11.5k samples against 19.5k before (also machine-dependent).
- **Where time goes now (samply, n=64, categories by innermost owner, overlapping stacks attributed to the first owner found).** `infer_rc` and its memo 44% (21% compute, 12.5% hashing, 10.6% alloc/drop), `shift` 12.6% (mostly allocation), `instantiate_n` 9.6%, `InferCache::enter` 8% (6.3% hashing), `whnf`/`whnf_step`/`eq_noting`/`conv` 15%, `expect_pi`/`expect_sort` 5%, `ctx_lookup` 1.3%. By kind: compute 47%, allocation and drop 30%, hashing 22.5%.
- **Infer memo statistics (whole check; `INFER-MEMO` lines).** n=32: 4.2M `infer_rc` calls, of which 2.48M single-reference (skip the memo), 875k hits, 855k misses (a lookup plus an insert), and 1.23M binder entries (`enter`). Memo hit rate on the calls that use it is 51%, so the memo earns its cost; each hit skips inferring a subtree.
- **Reading.** `ctx_lookup` (the shift I proposed memoising) is 1.3% of time and `subst_top` in the `App` rule is inside `infer` proper: the `App` rule's substitution is inherent (the type of `f a` is `cod[a]`), and delaying it as a redex would push the beta into every one of the 7.8M `def_eq` calls. Remaining constant-factor options, none tried: look the memo up by raw pointer without cloning the `Rc` key (saves a refcount touch per call), one hash for a miss instead of a get then an insert, interning binder contexts without hashing every entry. Growth is still the proof term's node count (about n^2.6), so a constant-factor change moves the curve down, not its slope; a smaller proof term from the generator is the other lever.
- **Probes added.** `INFER-MEMO` counters (walk slots 18 to 21), `whole_check_time` (ignored test, best of 3 at n=32 and 64).

## 49. Research: closure-based Lean kernels (nanoclo, sokonanoda) against our measured profile (2026-09-30)

**Sources and their reliability.** Lean Kernel Arena pages for `nanoclo`, `sokonanoda`, `nanobruijn` and the `perf/app-lam` and `perf/shift-cascade` tests, and the `sgraf812/nanoclo` README, all read through a small-model summariser. The checker descriptions (verbatim, confirmed on a second fetch): nanoclo, "a Lean 4 kernel based on delayed substitutions. Terms in flight are closures over interned environments. Entering a binder extends the environment in O(1); a variable occurrence reads its entry through skew-binary jump pointers; substitution into a body happens only when a type leaves the checker"; sokonanoda, "conversion checking uses closures", a distant fork of nanoda inspired by smalltt. Timings are the arena's, against the arena's baseline (the official C++ kernel); I did not open run logs or source. Both checkers were written under AI direction (the arena pages say so), and one nanoclo test (a Mathlib run) failed, so these are experimental.

**What the designs do.**
- *nanoclo.* Types and terms in flight are (expression, interned environment) closures. The `infer` memo is keyed by the term plus only the bindings it references, not the whole context, so a subterm reached through different binder stacks that agree on what it uses is inferred once. Conversion evaluates both sides into an interned value graph (equal values compare as integer indices), with thunks (each argument evaluated at most once), constants unfolded at most once per instantiation, and a step budget that abandons speculative argument comparison in favour of unfolding. Substitution is performed only when a type leaves the checker. Reported: `perf/app-lam` 12 to 23 ms (÷388 vs the arena baseline), `perf/beta-ladder` ÷271; the Mathlib run failed after 4.7 minutes.
- *sokonanoda.* Closure-based conversion following smalltt's normalisation by evaluation; reported ÷10 on `shift-cascade` (4 ms), ÷15 on Mathlib (1.2 min), ÷12 on CSLib, ÷8.4 on Cedar, with higher memory (Cedar +84%); passes all 69 soundness and 132 completeness tests.
- *`perf/app-lam`'s own account of the problem.* Without an infer cache, shared subterms cost O(2^n); with one, inferring each lambda still substitutes into a body of size O(n) at each of n levels, O(n^2). That is the `App`-rule substitution in our `infer` (§47: 7.4M of 18.1M `instantiate` visits at n=64).

**Fit with our measurements.**
- Our kernel's `def_eq` is 15% of a whole check (§47), so a closure-based conversion in the style of sokonanoda would address the 15% that §37 to §45 already cut by fusion; `kernel_lazy.rs` (§32) is that style and was level with the kernel from n=32, only a constant factor.
- The infer side is the larger share: `infer_rc` memo and its hashing 19% plus allocation, `App` substitution about 5%, binder-entry interning 8%. nanoclo's two infer ideas address those directly: O(1) delayed substitution at `App` (our `subst_top(cod, a)`), and a memo key that depends only on referenced bindings (our key is (pointer, whole-context id); the 51% hit rate in §48 is the rate within one context).
- Cost and risk: both are rewrites of `infer` into an environment-based form; the second needs the dependency closure of a node's referenced bindings (a binder's type can mention earlier binders), which is the hard part of a relevance key; neither is a local patch. The reported gains are against a baseline that is not ours (§41 to §48 already took the kernel's own constant factor down), so the arena ratios do not transfer.
- Reflection (proof by computation) is the standard route to smaller proof terms (a polynomial reduction in term size at the cost of reduction time during checking, in the sources searched); our proof is already by reduction. The bit-width-independent proof literature (Niemetz et al. 2019; SMT with non-linear integer arithmetic and quantifiers) works in SMT solvers, not a kernel, and does not give a kernel recipe for induction on width.

**Candidate experiments, in rising cost** (none started): (a) memo lookup by raw pointer and a single hash per miss (§48); (b) measure, with a probe, how many infer misses would hit under a relevance-keyed memo (count, for each miss, whether the same node was inferred under a context that agrees on the last `loose()` binders and their dependencies); (c) delay `App` substitution by returning a closure-typed result only where it is not immediately compared; (d) closure-based `infer` as a whole (nanoclo's design).

## 50. Probe: a relevance-keyed infer memo would remove almost every miss (2026-10-01)

- **Question (§49 candidate b).** `infer_rc` keys its memo by (node pointer, whole-context id). nanoclo keys by the node plus only the bindings it references. How many of our strict misses would a relevance key turn into hits?
- **Probe.** Behind `record-defeq`, `InferCache` records for each context id its parent, binder-type pointer and that type's loose range. For each memo-eligible lookup (a node with more than one reference), `relevant_signature` takes the node's loose range, closes it over the loose ranges of the binders' own types (a binder's type can mention earlier binders), and hashes the pointers of that window of innermost binders. A (node pointer, signature) seen before, with the strict key absent, counts as an extra hit. `RELAXED-MEMO` lines.
- **Result (whole check, n=8/16/32/64).** Strict misses 48k / 207k / 855k / 3.47M; extra hits under the relevance key 46.7k / 203k / 847k / 3.45M, i.e. 96% to 99.5% of the strict misses. Of the extra hits, nodes with no loose variable at all (closed) are 19.6k / 85.4k / 356k / 1.45M (42% at n=64). The mean window is 0.7 to 0.8 binders: nodes depend on almost none of their context.
- **What it means.** The same shared node is being re-inferred in every binder context that differs only in outer binders it never mentions. At n=64 that is 3.45M inferences, each also skipping its single-reference subtree, against roughly 15k that a relevance key would need. Hit rate under the strict key is 7.42M / (7.42M + 3.47M) = 68% already counting hits only among eligible calls; the relevance key would bring it to about 99.9%.
- **Soundness of the simplest version (not implemented).** For a node with no loose variable (`loose_of(e) == 0`), `infer`'s answer cannot depend on the context: no `Var` is looked up, a closed term has a closed type, and `Const` types come from the call's fixed `globals`. So its memo key can use context id 0. That alone covers 1.45M of the 3.45M extra hits at n=64. The windowed version needs the dependency closure above and a way to intern a window as an id; the probe shows its payoff (the other 2.0M) but not the cost of computing keys (mean window under 1, so small).
- **Caveats.** The probe records every lookup in its relaxed set, including ones the strict memo answered, so "seen before" means a stored result would exist; it does not verify the stored result is valid for the new context, which is exactly what the soundness argument above is for. Pointer identity of binder types stands in for equal types (as `enter` does), so it may undercount real equality. No timing was taken; the win is in inferences avoided, not yet in seconds.

## 51. Relevance-keyed infer memo (implemented) and re-profile

- **Change.** `infer_rc` keys its memo by (node pointer, `memo_context(cid, e)`) instead of (node pointer, whole-context id). `memo_context` returns the shared window id `WINDOW_BIT` for a closed node, and otherwise interns the window of innermost binders (by binder-type pointer) that the node can reach, closed over the loose ranges of those binder types. It falls back to the whole-context id when the window meets a `fresh` binder, runs into the caller's context (cid 0), or exceeds `MAX_WINDOW` = 8.
- **Since changed (2026-10-14).** `MAX_WINDOW` is gone, and the window now starts at the node's lowest loose variable rather than at the innermost binder: the key is (node, lowest loose variable, window above it). Rule-law proofs nest about 6n binders, so nearly every lookup had fallen back to the whole context, and shared subterms of J motives sat under per-use binders they never mention. See `docs/tier-cycle.md`, "Why checking a law slowed faster than it grew".
- **Soundness.** A node's inferred type depends only on the binder types it reaches through its loose variables, and each binder type may in turn mention outer binders, which is why the window is closed over their loose ranges. Closed nodes depend on nothing but `globals`. `infer_memo_changes_no_answer` (100,000 random terms, with and without the memo) shows no differing answer; 104 kernel tests pass.
- **Effect (n=64, visit counts).** Memo misses 3.47M -> 4,237; hits 7.93M. Whole-check visits: instantiate 18.1M -> 12.9M, shift 14.9M -> 13.2M, eq 50.8M -> 49.2M.
- **Time (whole check, best of 3, interleaved A/B, machine shared with another session's `manifold`, so noisy).** n=32: base 1.0-1.34 s, closed-only key 0.48-0.70 s, windowed 0.46-0.53 s. n=64: base 7.6-10.1 s, closed-only 4.7-6.2 s, windowed 4.6-5.0 s. The windowed key adds little over closed-only in seconds despite removing 3.4M misses.
- **Re-profile (samply, n=64, windowed build; CPU 23% at start, Defender real-time protection off).** Self time by outermost function: `infer_rc` 10.0%, `loose_of` 8.2%, `shift_child` 8.2%, `same_shape` 7.2%, drop glue 6.1% + 3.0%, `infer_node` closure 5.6%, `instantiate_n` 5.2%, `check_rc` 4.8%, hashbrown table drop 4.1%, `Expr::clone` 4.0%. Inclusive: shift 24.9%, `Rc::new` 19.2%, `def_eq` 18.1%, `instantiate_n` 14.5%. No single hot spot is left: allocation and drop of shifted terms (~20% `Rc::new`, ~9% drop glue) and `loose_of`/`Rc::loose` (~12% combined, recomputed rather than cached on a node) are the biggest items.

## 52. Shifted nodes reuse the known ranges

- **Finding.** �51 assumed `loose` was not cached; it already is (`Node.loose`/`free`). The ~12% in `loose_of`/`Rc::loose` was recomputation: `shift_child` built each shifted node with `Rc::new`, which re-ran `loose_of` and `free_of`, and `shift` re-checked `loose_of` on a child `shift_child` had just checked.
- **Change.** `shift_child` calls `shift_unchecked` (no repeated check) and builds the node with `Rc::with_ranges`: its largest loose variable is at or above `cutoff` and moves by exactly `amount`, so the new range is `loose + amount`; `free` is unchanged. Saturated ranges (`u32::MAX`) fall back to `Rc::new`. A `debug_assert` checks the supplied ranges against `loose_of`/`free_of`; the 104 kernel tests pass in debug and release.
- **Time (whole check n=64, best of 3, three interleaved alternations, CPU 25% from another session):** before 5.40, 5.61, 5.32 s; after 4.93, 5.22, 5.17 s. About 3-9% faster.
- **Not done:** the remaining shift cost (25% inclusive) is allocation of shifted copies for context arguments; �44 found those arguments mention only the checker's context and �43 that a shift memo saves ~1%, so no further shift change is justified by the data.

## 53. Scaling after �51-52

`add_zero_lemma_scaling` (release, CPU ~20% from another session, Defender RTP off): n=8 8.5 ms, 16 61 ms, 32 0.50 s, 64 4.7 s, 128 42.8 s. Each doubling costs about 8-9x (roughly n^3.1-3.2), so the check is still superlinear; the constant is down but the exponent is not. `instantiate_n` was not changed: its result nodes' ranges depend on the arguments, and `Rc::new` reading cached child ranges is cheap next to the allocation itself.

## 54. The cubic growth is the proof's size, not the checker

- **Measured** (`SIZE` line in `walk_counts_on_hard_queries`, via `kernel::term_sizes`; record-defeq): proof DAG nodes n=8 27k, 16 150k, 32 1.05M, 64 8.03M (ratios 5.5, 7.0, 7.7, toward 8); statement DAG 2.8k, 5.6k, 11.3k, 22.6k (linear). Whole-check visits grow by the same ratios (n=32 to 64: instantiate 7.8x, shift 7.8x, eq 7.7x, infer binder entries 7.8x). So check cost is about linear in the proof DAG, and the generator's proof is O(n^3) in a statement of size O(n). Checker tuning cannot change the exponent.
- **Where the proof grows (analysis, not yet measured).** `cong_n` (`kernel.rs`) rewrites one of the n sum bits per step. Each step builds `g = \z. f x_0 .. z .. x_(n-1)` with `shift(a, 0, 1)` of every other argument, then `cong1` shifts `g` by 1 and 3 and `trans_proof` shifts `lhs_all` by 1-3. The arguments are the sum bits `s_j` (DAG size O(j): they contain the carry chain `c_j`, which is shared) and mention context variables, so every shift makes fresh copies: n steps x n arguments x O(n) per argument = O(n^3), where the copies are the same terms shifted by the same amounts again in each step.
- **Candidate fix (not started).** A shift memo keyed by (node pointer, cutoff, amount), shared across the steps of one `cong_n` call and passed into `cong1`/`trans_proof` internals, so each argument is shifted once per (cutoff, amount); the DAG would then be O(n^2) and the check should follow. Needs a differential test that the memoised builder returns terms equal to the current one.

## 55. Memoised shifts in `cong_n`: proof DAG 5x smaller at n=64

- **Measured first (n=32/64, temporary probe, removed).** Each `cong_n` step's `cong1` output is 25-42k DAG nodes at n=32 and 82-125k at n=64 (about 25 n^2 each); n steps of that is 6.4M of the 8.0M proof nodes at n=64. So the shifts in `cong_n` are the main source of the cubic term, as �54 reasoned.
- **Change.** `ShiftMemo` and `shift_memo` (a (node pointer, cutoff, amount) memo that keeps source nodes alive), via `shift_via`, which is `shift`'s walk with the per-child step passed in (the hot `shift` still passes `shift_child`). `cong_n` owns one memo and passes it to the new `cong1_in`/`trans_proof_in`; public `cong1`/`trans_proof` make a fresh one, so callers elsewhere (`proof.rs`, tests) are unchanged. The proof term is the same (tree size identical at every n); only sharing differs. Test `shift_memo_matches_shift`: 20,000 random terms, one memo across cutoffs 0-3 and amounts 1-3. All 353 library tests and the integration tests pass.
- **Result.** Proof DAG nodes n=8 16.6k, 16 54.8k, 32 254k, 64 1.58M (was 27k, 150k, 1.05M, 8.03M). Whole check (CPU about 20% from another session): n=8 4.7 ms, 16 26 ms, 32 160 ms, 64 1.28 s, 128 11.6 s (was 8.5 ms, 61 ms, 0.50 s, 4.7 s, 42.8 s). That is 3.7x faster at n=64 and n=128.
- **Still superlinear.** Doubling now costs 8.4-9x in time and the DAG ratios are 3.3, 4.6, 6.2, so a cubic piece remains in how the generator builds the proof.

## 56. `trans_proof`'s `arrow` copied the shifted `x`; proof DAG now O(n^2)-ish, but check time is not DAG-bound

- **Phase probes (temporary, removed; n=64).** The inputs to `cong_n` (carry chain proofs `pc`, bit proofs `e`, sums `s`) total about 230k DAG nodes; `cong_n`'s output was 1.55M, growing ~22-26k nodes per step. A dummy-proof `trans_proof` showed 20.5k new nodes per call, all in its motive, though `shift_memo(x, ..)` was verified to return pointer-shared results. Cause: `arrow(A, B)` is `pi(A, shift(&B, 0, 1))`, and that plain `shift` copied the already-shifted `x` (18k nodes) afresh at every call. (An earlier "union" probe through `mk` was misleading: `mk` shifts its arguments, so it measured its own copies. Unions must use a shift-free pairing, `app`.)
- **Change.** `trans_proof_in` builds its arrow as `pi(a, shift_memo(b, 0, 1))`. `cong1` has no `arrow`.
- **Proof DAG nodes** n=16 35.8k, 32 96k, 64 288k, 128 954k, 256 3.42M (�55: 54.8k, 254k, 1.58M, 11.4M, 87.0M). Ratios per doubling 2.7, 3.0, 3.3, 3.6, heading to 4. New ignored test `proof_size_scaling` (record-defeq) prints this without checking.
- **Time.** Interleaved A/B against the �55 build, whole check n=64: new 1.67, 1.75, 1.56 s vs old 1.81, 2.19, 2.26 s (the machine was slower than during �55 even at 7-10% CPU, so absolute times are not comparable to �55). `add_zero_lemma_scaling`, old vs new: n=64 2.40 vs 1.77 s, n=128 22.4 vs 19.3 s. 353 library tests pass.
- **What this shows.** The proof is now ~quadratic in size, yet check time still grows 8-11x per doubling, and the n=64 whole-check visit counts that are not about the proof's own DAG are unchanged: instantiate 12.9M, shift 11.7M (�51: 12.9M, 13.2M; eq fell 18.5M -> 12.4M, infer-memo binder entries 1.08M -> 342k). Those walks happen in def_eq queries and in `infer`'s application rule (`instantiate` of codomains per context), which see a shared node once per distinct context, not once per allocation. So the remaining cubic cost is in how many (node, context) pairs the checker visits, not in the proof's size.

## 57. Re-profile after the proof shrank, and where the cubic visits come from

- **Profile (samply, n=64, build 7a30e99; 2,002 samples against 8,381 in �51's).** Inclusive: `instantiate_n` 33.7%, `def_eq` 30.5% (`conv` 27.9%), `shift_via` 20.5%, `Rc::new` 21.3%. Self time by outermost function: `same_shape` 16.0%, `instantiate_n` closure 14.4%, `shift_child` 13.9%, `drop_slow` 9.3%, `loose_of` 9.2%, `infer_rc` 4.6%. The infer memo and hashing no longer dominate (they were ~44%); the substitution and comparison walks do.
- **The visit counts that did not change when the proof shrank** (n=32 -> 64, all about 7.5-7.8x): instantiate sites `other` 685k -> 5.36M, `app_subst` 300k -> 2.25M, `def_eq` 677k -> 5.3M; `def_eq` also does 3.7M shift and 4.4M eq visits at n=64 (conv betas 5,980 -> 20,156 = 3.4x, so about n^2 betas at about n visits each). Reading: `infer`'s application rule does `subst_top(cod, a)` where the codomain mentions O(n)-size carry terms, once per (App node, window) pair, and there are O(n^2) such pairs; the conversion does O(n^2) beta steps each substituting an O(n)-size term. Both are n^2 operations on O(n)-size terms, which an eager, copying substitution pays in full. Reaching O(n^2) overall would need the substituted result to share structure with its inputs (�49's closure/delayed-substitution designs), not a cheaper walk. This is a reading of the counts, not a separately measured per-site breakdown by term size.
- **Other `cong1`/`trans_proof` call sites.** `proof.rs` calls `cong_n` and `trans_proof` once each (lines 1861-1866) and gets `cong_n`'s memo for free; its own `arrow` uses and the per-bit `cong1`/`trans_proof` chains in `tests/church_bv.rs:276-295` (inputs of about 230k of 288k nodes at n=64) still use fresh memos and could share one, at most halving the proof, with no change to the exponent.

## 58. Probes for hash-consing and a global `instantiate` memo

- **Method (record-defeq; `hc_probe` in `kernel.rs`, `HC` and `INST-MEMO` lines in `walk_counts_on_hard_queries`).** Each node built by `Rc::new` gets the id its structure would have in a hash-cons table (64-bit hash of constructor, leaf value, and children's ids; the table is not cleared, so nodes equal to ones built earlier, including the proof's, count as hits). `instantiate_n` calls are keyed by (id of the term, ids of the arguments, depth); a repeat is a call a global memo would have answered, and "visits skipped" is the visits inside the maximal repeated calls. Nothing changes results; times in that run are inflated by the probes.
- **Hash-cons hit rate during the whole check.** Nodes built / structurally new: n=8 61,571 / 1,152 (98.1% hits); n=16 418,671 / 2,448 (99.4%); n=32 3,141,895 / 6,008 (99.8%); n=64 24,509,239 / 16,200 (99.93%). The number of distinct structures grows about 2.5-2.7x per doubling (n^1.4), while nodes built grow about 7.8x (n^3).
- **Global `instantiate` memo.** Visits skipped / all `instantiate` visits: n=8 27,214 / 34,534 (79%); n=16 197k / 225k (88%); n=32 1.56M / 1.66M (94%); n=64 12.50M / 12.92M (96.7%). Maximal repeated calls at n=64: 101,362; top-level calls 16,595, 14,435 of them repeats. The skipped share rises with n, so a memo's gain grows with n.
- **Reading.** The check's cubic work is almost entirely re-doing identical structural operations: it builds the same 16k distinct nodes 24.5M times and instantiates the same (term, arguments, depth) triples over and over. That supports hash-consing plus pointer-keyed memos of `instantiate`, `shift` and `whnf` as a general replacement for the per-case sharing fixes (�48-�56), and suggests the cost could fall toward the number of distinct structures. Not shown: `shift`, `whnf`, `def_eq` and `infer` repeat rates (only `instantiate` was probed beyond the build count); the real cost of the intern lookup against the `Rc::new` it replaces; whether an interned design keeps these rates when `infer`'s context windows are part of the key (the infer memo already covers that part: 99.5% hit rate, �51).

## 59. Repeat rates of the other operations, intern cost, and a lifetime policy

- **Repeat rates (record-defeq, whole check; `REPEAT` lines).** Work a global memo keyed by structure would skip, by operation, n=32 / n=64: `instantiate` 93.6% / 96.7% of 12.9M visits; `shift` 99.7% / 99.9% of 11.7M visits (145,645 maximal repeated calls at n=64); `whnf_step` 99.4% of its 1.15M calls repeat, but the work inside the maximal repeats is only 35% of all walk visits at both sizes (nested instantiate and shift work is counted once, at the instantiate/shift level); `conv_whnf` 9.6% (130 of 1,093 top calls repeat, 0.95M of 9.9M visits). So the structural operations (shift, instantiate) repeat almost completely; the comparison of two normal forms mostly does not repeat on identical pairs, and its cost is dominated by the whnf work inside it.
- **Intern cost (`intern_lookup_vs_rc_new`, ignored; 16M App nodes over 16k leaves and 64k distinct pairs, pointer-keyed map with the multiply-rotate hash, machine lightly loaded).** `Rc::new` (allocate, compute ranges, drop) 144 ns per node; an intern hit 33 ns, table of 65k entries. With a real hit rate above 99.9% a hit replaces nearly every allocation. Caveat: the pool is small and cache-resident; the real table at n=64 has 16k entries, so it should stay so.
- **Lifetime policy (design, not implemented).**
  1. Interning is an optimisation, never a correctness requirement: the table's key is exact (constructor, leaf value, child pointers), so two nodes merge only if they are structurally equal, and structurally equal nodes that were built outside the table simply stay distinct. Pointer equality stays a fast path in front of the structural comparison, as now. Soundness is unaffected by a missed merge.
  2. Scope: one table per `check` (and per standalone `def_eq`/`infer`), held by the same object as the infer memo and dropped with it. The table's own references are the only extra counts; nodes handed back to callers (inferred types, normal forms) stay alive through their own `Rc`s. At n=64 the table would hold about 16k nodes, so no eviction is needed inside a check; an unbounded workload per check would need a size cap that clears the table (and every pointer-keyed memo with it).
  3. Where to intern: nearly every node built in the check comes from `instantiate_n` and `shift` (24.5M builds against 12.9M + 11.7M visits), so interning only their child construction (`go` in each) captures the rate; builders and the input proof stay as they are and get canonicalised the first time a substitution or shift passes through them. Roots are plain `Expr` values, so a memo keyed on a root argument needs it wrapped in an interned `Rc` first (one lookup).
  4. Costs to handle: `infer_rc` skips its memo for `Rc::strong_count == 1`, and the table's reference makes every interned node count as shared, so that test must look at something else (for example "built by the table"); `Expr`'s iterative `Drop` already handles any drop order, so clearing the table is safe for deep chains; the table is thread-local like the other caches (`Rc` is not `Send`).
- **Open.** A prototype behind a feature flag: intern in `instantiate_n`/`shift_via` children, memoise both by (node, arguments, depth) / (node, cutoff, amount), and A/B at n=32 and 64. The probes bound the gain from above (they ignore the table's lookup and memo-key hashing costs).

## 60. Hash-consing prototype (`hashcons` feature): result

- **What it is** (`mod hc` in `kernel.rs`; Cargo feature `hashcons`, off by default; with it off every `hc::` function is a no-op and the code is as before). Inside a `hc::Scope` (opened by `check_in`, `infer_in`, `def_eq`; the table and memos are dropped with the outermost scope) `instantiate_n` and `shift_child` intern the nodes they build under an exact key (constructor tag, leaf value, child pointers) and memoise: `instantiate` by (source node, argument-list id, depth), `shift` by (source node, cutoff, amount); each memo entry keeps its source node alive, so a freed address cannot give a false hit. Argument lists get an id from their interned nodes (one argument: its node's address; several: an odd table id). Per section 59, a missed merge only loses sharing.
- **Correctness.** All 353 library tests and every integration test pass with the feature on; the default build is unchanged (353 pass). The differential test `infer_memo_changes_no_answer` and the random `shift`/`instantiate` tests run on the interned path too.
- **Visit counts, whole check at n=64 (record-defeq + hashcons).** instantiate 12.9M -> 0.79M (16x fewer), shift 11.7M -> 0.32M (36x), eq 12.4M -> 7.96M; infer-memo misses 59.9k -> 332k (interned nodes count as shared, so more calls take the memo path).
- **Time (interleaved A/B, machine loaded by another session: 45-90% CPU at start, Defender RTP off).** Whole check n=64: off 1.59-2.40 s, on 0.89-0.98 s; n=32: off 0.20-0.30 s, on 0.16-0.23 s. `add_zero_lemma_scaling`, off vs on: n=8 5.1 vs 9.4 ms, 16 28.6 vs 38.3 ms, 32 211 vs 181 ms, 64 1.76 vs 0.92 s, 128 13.2 vs 5.7 s. So 1.9x at n=64 and 2.3x at n=128, a loss below n=32 (table setup and lookups on small terms), and per-doubling growth 7.5x -> 6.2x. Whole-check samples (samply, n=64): 2,002 -> 1,143.
- **Profile of the `on` build (n=64).** The intern machinery is now about 30%: `hc::intern` 12.8% self, `make_hash` 6.2%, table rehash 4.4%, `key_of` 5.4%, `hc::inst_get`/`inst_put` 6.8%. The rest: `infer_rc` 10%, `same_shape` 8.6%, `InferCache::enter` 4.2%. `eq` is still 8M visits and is now the largest walk.
- **Not done / open.** Cheaper keys (hash the table key once, avoid `same_shape` in `key_of`), pre-sizing the table to avoid rehashing, skipping interning for tiny scopes; making `eq_noting`/`same_shape` exploit interning (children from the table that are pointer-unequal are structurally unequal when both are interned: a fast negative); revisiting `infer_rc`'s `strong_count == 1` shortcut, which interning defeats; making `hashcons` the default once it wins at all sizes the repo checks.

## 61. Hash-consing: cheaper table, canonical negatives, `strong_count` shortcut

- **Table cost.** `key_of`'s `same_shape` walk is replaced by a direct match over the constructor's children (`for_kids`), the lookup uses one `entry` (one hash on a hit or a miss), and the table switches on only after `WARM_UP` = 3,000 non-trivial `instantiate_n` calls in a scope (a smaller check would only pay for it; unit tests set it to 0 so the differential tests exercise the table). The node gains a `generation` word under the feature (56 -> 64 bytes; `a_node_is_56_bytes` follows `cfg!`).
- **Canonical negatives.** A node is canonical when the table built it and all its children are canonical, and carries the table generation (never reused, so nodes that outlive a scope stop being canonical when it ends). Two canonical nodes are structurally equal exactly when they are the same node, so `Expr`'s `==` and `eq_noting` answer "unequal" for distinct canonical children without walking. Effect on the check is nil so far: n=64 `eq` stays at 7.96M visits, because the operands of the hot comparisons are an inferred type (built by `instantiate`, canonical) against an expected type taken from the proof (never interned). Interning the checked term and claim when the table switches on would make both sides canonical; not done.
- **`infer_rc`'s `strong_count == 1` shortcut.** Tried treating canonical nodes as unshared up to 1, 2, 3 or 4 references (the table and memos hold extra counts): whole check n=64 0.73-0.80 s at every setting, no lever (the experiment read an environment variable per call, so its absolute times are inflated; reverted). Misses stay 332k at n=64.
- **Time (interleaved, `add_zero_lemma_scaling`, CPU 15% at start, Defender RTP off), off vs on:** n=8 4.0-4.5 vs 5.4-6.2 ms, n=16 22.6-28.5 vs 31.5-36.5 ms, n=32 167-176 vs 169-174 ms, n=64 1.46-1.49 vs 0.83-0.92 s, n=128 10.9-11.8 vs 4.05-4.5 s (about 2.5x). Small widths are still slower with the feature on (n=8 does not even switch the table on, so what it pays is the scope and the larger node, and a few ms are within noise); the crossover is near n=32.
- **Still open.** Intern the input term to unlock canonical negatives; shrink the per-scope fixed cost; make `hashcons` the default only if the small-width loss is closed or accepted.

## 62. Interning the inputs; `hashcons` becomes the default

- **Change.** `check_in` now canonicalises the checked term and the claim (`hc::canonical_inputs`) when they have more than 3000 distinct nodes (every input under `cfg(test)`): it switches the table on at scope entry, then rebuilds both bottom-up through a pointer memo with `intern`. Both sides of the hot `def_eq`/`eq_noting` comparisons are then canonical, so distinct canonical nodes answer "unequal" without a walk. Inputs below the bound keep the lazy `WARM_UP` switch-on. The result is the same `Expr`s, structurally.
- **Time (best of N, CPU load 25% at start, Defender RTP off), default build vs `hashcons`:** n=16 27.3-27.7 vs 16.2-16.5 ms; n=32 `add_zero_lemma_scaling` 214 vs 86 ms, `whole_check_time` 152-176 vs 57-68 ms; n=64 1.61 s vs 0.38 s (`whole_check_time` 1.36-1.47 vs 0.28-0.35 s); n=128 14.3 s vs 1.59 s (the 10x). n=8 is a tie (4.2-4.8 vs 4.8 ms, within noise). Before this change the feature gave 2.5x at n=128 (4.0-4.5 s); canonical inputs add a further 2.5-3x. Note the default-build n=128 figure is higher than section 61's 10.9-11.8 s because of machine load; the ratio is the result.
- **Profile, n=128 with the feature (1864 samples, samply):** `hc::intern` is 43.5% inclusive, of which `hc::canon` (input canonicalisation) is 19.5%; hash-table probing (`find_inner`, `write_u64`, `reserve_rehash`) dominates its self time; `instantiate_n` 49%, `whnf`/`beta_spine` 29-37%. So the remaining cost is mostly the table itself, not the checker's own walks.
- **Decision: `hashcons` is on by default** (`default = ["hashcons"]`; `--no-default-features` turns it off). The small-width loss from section 61 is gone (n=16 and up are faster, n=8 ties), and the gain is 2.5x at n=32 and 9x at n=128. Both configurations pass the whole test suite. The probe feature `record-defeq` is unchanged.
- **Still open.** `canon` is a fifth of the n=128 profile: input interning could run once per proof rather than per `check_in` call, or the proof builder could intern as it builds. Table hashing: `NodeKey` is 48 bytes hashed with a general hasher; a node-id scheme (dense ids, children by id) would shrink and speed it. The table is rebuilt per outermost scope.

## 63. Input interning cost, cheaper key hash, n=256

- **`canon` already runs once per check**, so "intern once per proof" is not a saving: `check_in` interns the DAG a single time through a pointer memo. Measured (temporary timer): 2.3 ms at n=8 (14k DAG nodes), 16 ms at n=32 (96k), 63 ms at n=64 (288k), 244 ms at n=128 (954k), about 250 ns per DAG node, 15% of the n=128 check. It only shrinks if the proof builder interns as it builds (the proof is built outside the kernel); not done.
- **`NodeKey` hash.** The derived `Hash` mixed eight words per lookup (tag, leaf, the array's length, five kids); a manual impl mixes six. n=128: 1.41-1.42 s vs 1.54-1.56 s (about 8%, CPU about 26%, Defender RTP off, interleaved). Kept. Dense node ids (children by id) not tried: the saving would be at most the remaining key size, and ids would need a side table.
- **n=256** (`add_zero_lemma_scaling` now goes that far): 6.64 s; times per width 3.9 / 14.5 / 54 / 252 ms / 1.21 s / 6.64 s for n=8..256. Growth per doubling 3.7, 3.8, 4.6, 4.8, 5.5: still climbing toward cubic (n^2.46 over the last doubling) while the proof DAG grows 3.3x per doubling (n^1.7), so the checker does superlinearly more work per proof node as n grows.
- **Still open.** Where the n=256 time goes (re-profile; the table, `whnf`/`beta_spine`, or `Rc` drop of the large intern table at scope exit); proof builder interning.

## 64. n=256 profile: the instantiate memo was 10M entries, 99% for nodes the arguments never reach

- **Profile, n=256 (6399 samples):** `hc::intern` 36% inclusive, `RawTableInner::find_inner` 30%, `NodeKey::eq` 11% self and `_mm_movemask_epi8` 11.5% self (table probing, cache misses), `hashbrown::reserve_rehash` 6%. The node table is small (351k nodes at n=256), so the misses were elsewhere: a temporary print at scope exit showed the **`instantiate` memo at 10.09M entries at n=256 (2.52M at n=128, 4x per doubling)** against 93k shift entries and 4k argument sets.
- **Hit rate 17%** (2.0M hits, 10.1M misses at n=256), so almost every entry was a one-off. A probe (does the source node mention a loose `Var` in `[d, d+m)`?) classed **98.8% of the misses as irrelevant**: 10.0M vs 82k relevant at n=256 (99.2% at n=64). For such a node the answer is `shift(x, d+m, -m)`, whatever the arguments, but the memo key included the argument id, so each of about 29 argument lists per node made its own entry and its own copy-and-intern walk.
- **Change.** `hc::uses(x, d, m)`, memoised per (node, depth, count) with the node kept alive in the entry, decides relevance; `inst_rec`'s child step returns `shift_child(x, d+m, -m)` (through the shift memo, shared across all arguments) when it is false. With the feature off `uses` is a stub returning true.
- **Time (CPU about 26%, Defender RTP off), before vs after:** n=64 0.21-0.25 s to 0.10-0.14 s; n=128 0.98-1.21 s to 0.41-0.48 s; n=256 5.4-6.6 s to 1.8-2.4 s. Growth per doubling is now about 4x (n=128 to 256: 4.4x) instead of 5.5x. Both configurations pass the whole suite.
- **Not a gain:** a pointer hasher for `canon`'s memo (n=128 0.478 s against 0.41-0.45 s, within noise); reverted.
- **Where the time is now (to re-profile):** `canon` was 244 ms of the n=128 check before this change; if it is still about that, it is more than half of what remains at n=128, so the proof builder interning as it builds is now the largest single item (and sits outside the kernel).

## 65. Re-profile after section 64; pre-sizing and a coarser infer key do not help

- **Profile, n=256 (3000 samples, 3.0 s):** `hc::canon` (interning the inputs) is **32% inclusive**, now the largest single item; `hc::intern` 25%, of which `reserve_rehash` 12% (tables growing); `infer_rc` 42% inclusive; `shift_via`/`shift_memo_child` 12-18%.
- **Pre-sizing the tables for the input (tried, reverted).** Counting the input DAG and reserving the node table and `canon`'s memo for it made things slower: n=128 0.60-0.72 vs 0.39-0.46 s, n=256 2.9-3.6 vs 2.0-2.4 s (interleaved, CPU about 50%). The node table needs about 350k entries at n=256 against a 954k-node input, so the reservation over-allocates and spreads entries over more cache lines. Growth is not the cost to attack.
- **Visit counts, n=64 whole check** (feature on, canonical inputs): instantiate 24k, shift 31k, `eq` 350k. Section 61 had `eq` at 7.96M and instantiate 0.79M, so interning the inputs plus the argument-relevance shortcut cut `eq` visits 23x and instantiate 33x.
- **Coarser infer key (checked, no gain).** The relevance-keyed memo (`RELAXED-MEMO`) would add 129 hits to 91,636 strict misses at n=64 (0.14%); misses are 91.6k now (they were 332k at section 57's count). The memo is not where the time is.
- **Left.** The proof builder interning as it builds (removes most of the 32%) is the one sizeable item; it needs a table scope that spans the builder, an API change outside the kernel, and has not been done.

## 66. `canon` adopts unchanged nodes; n=512

- **Change.** When `canon` finds that a node's children all came back as themselves (leaves, or nodes whose children were already table nodes), it puts that node itself in the table (`intern_as` with a build closure that returns the existing `Rc`) instead of allocating a twin. This removes one allocation and one drop per adopted node; results are structurally the same. Suite passes.
- **Time.** Inconclusive: another session's load swung identical runs by 2x. Four interleaved pairs of exes (HEAD vs adopt, CPU 17% at start, Defender RTP off): HEAD best n=128 418 ms, n=256 2.23 s; adopt best 412 ms and 1.90 s; individual runs overlap (adopt 0.41-0.86 s, HEAD 0.42-0.65 s at n=128). Kept because it does strictly less work, with no measured regression in the best-of-4.
- **n=512** (now the top of `add_zero_lemma_scaling`, which takes about 24 s): 6.6x over n=256 (16.6 s), against 5.5x for 128 to 256 in section 63 and about 4.4-5x after section 64. Per doubling: 3.1, 3.3, 3.6, 4.1, 5.6, 6.6 from n=8 up. That is roughly n^2.7 over the last doubling and still rising, so a cubic-or-worse term remains at large n; with the DAG at about 3M nodes the tables no longer fit in cache, which may account for part of the rise (not measured).
- **Builder interning (not done).** Making the proof builder intern as it builds needs a table scope held across the builder and an intern call at each node construction in the cong/trans builders; it would remove most of `canon`'s share (32% at n=256) but is invasive and its saving is bounded by that 32%, which is small next to the growth above. Deferred until a profile at n=512 says what dominates there.

## 67. n=512 profile: the work is quadratic, the extra growth is memory

- **Work counts are quadratic, not cubic** (`walk_counts_on_hard_queries`, record-defeq build, n=32/64/128/256): `eq` visits 98k, 350k, 1.31M, 5.06M (3.6x, 3.7x, 3.9x per doubling); `instantiate` 9k, 24k, 73k, 244k; `shift` 11k, 31k, 98k, 344k; infer-memo misses 26k, 92k, 343k, 1.33M (3.5-3.9x); proof DAG 96k, 288k, 954k, 3.4M (3.0-3.6x). All sit near n^1.9.
- **Time splits into two phases** (temporary timers in `check_in`, n=64/128/256/512): input interning (`canon`) 70 / 304 / 1324 / 5121 ms (4.3x, 4.4x, 3.9x: tracks the DAG), checking 68 / 265 / 1612 / 10501 ms (3.9x, 6.1x, 6.5x). So the checker's time per unit of counted work grows about 1.6x per doubling at the top: not an algorithmic term but the memory system.
- **Memory.** Peak working set 620 MB at n=256 and 2195 MB at n=512 (3.5x). Tables at n=512 (post section 64): nodes 1.29M, inst 0.86M, shifts 1.00M, uses 0.84M entries (3.7x per doubling), and the 3M-node input held by the test plus its interned copy. Profile at n=512 (20282 samples): `canon` 26% inclusive, `intern` 17%, `infer_rc` 51%, 22% in non-app code (allocator and page faults).
- **Reading.** The kernel's work is now about n^1.9; the rest of the growth is cache and page-fault cost on a 2 GB working set. Levers by size: (a) not holding a second copy of the proof (builder interning, or `canon` adopting more, or freeing the input tree) cuts memory about a third and `canon`'s 26%; (b) smaller table entries (dense ids, 24-byte keys) cut the table share of memory; (c) neither changes the n^1.9 work. Not done; `profile_add_zero_n512` added for the next look.

## 68. Survey: interning in the proof builder; why section 67's step 1 and 2 are moot

- **Step 1 (avoid the second copy) rests on a wrong premise.** `canon`'s output is not a second full copy: temporary probe, input DAG nodes vs distinct structures (the interned result) at n=8/16/32/64/128/256/512: 14,441 / 35,833 / 96,281 / 287,833 / 953,561 / 3,415,513 / 12,861,401 against 1,143 / 2,435 / 5,595 / 14,219 / 40,683 / 130,475 / 457,515. The result is 12.6x to 28x smaller than the input and the ratio grows with n (20x at n=64, 28x at n=512). So the memory is the **input** held by the caller (about 12.9M nodes of 64 bytes, roughly 0.8 GB at n=512), plus `canon`'s pointer memo (13M entries while it runs). Nothing in the kernel can free the input: `check_in` takes `&Expr`.
- **Step 2 (smaller table entries) buys little.** Entry sizes at n=512 (post section 64): nodes 1.29M x 57 B = 74 MB, inst 0.86M x 41 B = 35 MB, shifts 1.0M x 33 B = 33 MB, uses 0.84M x 33 B = 27 MB, about 170 MB of tables plus about 83 MB for the nodes. Dense ids with 24-byte keys would shrink the first row by about a third, i.e. under 10% of the check phase's footprint. Not worth the table-of-ids side structure. That the check phase is cache-bound (section 67's reading) is still a hypothesis, not a measurement.
- **Builder interning, what it takes.** The kernel's public constructors (`pi`, `lam`, `app`, `id`, `refl`, `j`, `w`, `sup`, `wrec`, `sigma`, `pair`, `sigrec`; kernel.rs near line 709) take `Expr` by value and wrap each argument with `Rc::new`: 25 call sites. Replacing them with `hc::intern(x, None)` makes everything built through the constructors canonical bottom-up, because each argument's children are already table nodes and `intern` keys on (constructor, leaf, child pointers). Outside a scope `intern` is a plain `Rc::new`, so behaviour there is unchanged. The caller must hold one scope across the build and the check (`let _s = kernel::InternScope::enter()`, a public wrapper over `hc::Scope` that also switches the table on at once instead of after `WARM_UP`); `check_in` then finds `generation != 0` and `canon` returns immediately for canonical nodes, so its 26-32% share disappears and the memo that `canon` holds never exists. `cong_n`, `cong1_in`, `trans_proof_in` build through the same constructors and the shift memo they already use is `hc::shift_get`-compatible.
- **Options compared.**
  - *A. Intern in the constructors, caller-held scope* (above). Pros: proof DAG 12.9M -> 0.46M nodes at n=512, so about 0.8 GB less peak memory and no `canon` pass (5.1 s of 15.6 s at n=512); about 30 lines; behaviour identical outside a scope; soundness untouched (the kernel still checks every node; the canonical flag is set only when all children are canonical in the same generation); tables, shift and instantiate memos are shared between the build and the check. Cons: one hash lookup per constructor argument inside a scope (builder time rises, not measured); the caller has to opt in, so code that builds without the scope gets today's behaviour; the table lives until the scope ends, so a long scope that builds many proofs keeps them all; thread-local only.
  - *B. Weak-reference global hash-consing, always on.* Pros: no API change. Cons: a `Weak` per table entry, interplay with `Expr`'s iterative `Drop`, cost on every construction for every user including the many that never check a large term; cross-thread sharing needs a lock or per-thread tables. More invasive than A for the same gain.
  - *C. Memoise in the test's builder only* (reuse the same `Expr` for repeated sub-builds). Pros: no kernel change. Cons: reduces the input but the kernel still has to `canon` the rest; each builder needs it; does not generalise to the tactic framework.
  - *D. Status quo plus adoption* (section 66). Pros: done, no API. Cons: still holds the whole input and its memo.
  - *E. Make `check_in` take the input by value* and free it while canonicalising. Pros: peak memory roughly halves. Cons: a breaking API change for every caller (`proof.rs` and the tests call it with references), and the input is usually still needed afterwards.
- **Recommendation: A.** It is the smallest change that attacks both the memory and the `canon` time, and the measured 20-28x shrink says the builder repeats itself heavily. Open questions before building it: what the lookup costs the builder at n=256 (best measured by building with and without a scope), and whether `proof.rs`'s tactic builders go through these same constructors (grep shows `proof.rs` has 2 `Rc::new` sites, so they likely do).

## 69. Option A built: `InternScope` and interning constructors

- **What.** `kernel::InternScope::enter()` (public; wraps `hc::Scope` and switches the table on at once via `hc::activate`) held across building and checking a proof. The twelve public constructors (`pi`, `lam`, `app`, `id`, `refl`, `jelim`, `wty`, `sup`, `wrec`, `sigma`, `pair`, `sigrec`) now make children with `hc::intern_new` (plain `Rc::new` outside a scope or without the feature). `shift_memo_child` and the two `abstract_frees_in` sites use it too. Inside a scope `check_in`'s `canon` finds everything canonical and returns at once.
- **A first attempt left 76% non-canonical** (proof dag 9.9M against 12.9M unscoped at n=512): the proof builders (`cong_n`, `cong1_in`, `trans_proof_in`) build through `shift_memo_child`, which used `Rc::new`, so a debug walk (nodes not canonical, by constructor: `App` 9546, `Var` 1230, `Lam` 453, ...) showed almost every node outside the table. After interning those three sites the walk finds none, and the proof DAG equals the distinct-structure count from section 68 (457,512 at n=512).
- **Results** (`add_zero_lemma_scaling_scoped`; set `NO_SCOPE=1` for the unscoped control; interleaved, CPU 34% at the last run, Defender RTP off):
  - n=256 build + check: scoped 0.34-0.56 s + 1.6-2.1 s; unscoped 0.36-0.56 s + 3.5-4.0 s. The proof DAG is 130k nodes against 3.4M.
  - n=512: scoped build 1.9 s + check 11.3 s; unscoped 3.8 s + 21.4 s. Peak working set for a run of all widths to 512: 1.11 GB scoped, 2.40 GB unscoped.
  - Unscoped times above are higher than sections 64-66 reported for the same check (about 2.0-2.5 s at n=256): another session's load; the A/B is interleaved so the ratio stands, the absolute numbers do not.
- **Cost.** Builder time is not slower in a scope (n=256: 0.34-0.56 s either way): the lookup per constructor argument is paid back by allocating 26x fewer nodes. Without the feature the constructors are unchanged.
- **Not done.** `proof.rs` builders: they go through the same constructors, but a real tactic proof has not been run inside a scope; the table lives until the scope ends, so a scope across many proofs keeps them all.

## 70. Spike B: always-on global weak hash-consing (branch `spike-globalcons`, not merged)

- **What was built** (Cargo feature `globalcons`, implies `hashcons`; about 100 lines in `kernel.rs`). A thread-local table from exact node key (constructor, leaf, child pointers) to `std::rc::Weak<Node>`. `Rc::new` and `Rc::with_ranges` look the key up and return the live node when the weak upgrades, otherwise build a node and insert its weak. `Node<T>` gets a `Drop` that calls `T::unintern` (a new trait, with a bound on every `Rc<T>` impl, since Rust will not allow a `Drop` impl for `Node<Expr>` alone) which rebuilds the key from the dying node's children, still alive at that point, and removes the entry if its weak is dead (a newer live node may share the slot). `canonical()` is true for every node; `intern_as` and the scopes' node table are bypassed. `Rc` is `!Send`, so per-thread tables are sound; a stale entry whose upgrade succeeds is always a structurally equal live node, so reused addresses cannot cause a false hit.
- **Correctness.** The whole suite passes except two unit tests that assert the opposite of sharing: `infer_memo_changes_no_answer` ("the copy shares a node": it builds a deep copy on purpose to defeat pointer-keyed memos) and `close_is_linear_in_the_dag_of_a_shared_body` (an exact node count, 64 vs 93). Both would need rewriting to build non-shared copies by another route; global interning removes the observable pointer difference they rely on.
- **Time, large proofs, no scope held** (interleaved, CPU 45%): n=256 build + check, global 0.32-0.52 s + 1.4-2.2 s; default build with an `InternScope` (option A) 0.31-0.46 s + 1.6-2.0 s; global with a scope the same. So B matches A's gain without the caller doing anything.
- **Time, everything else (the cost of always on).** Whole-target test times (global vs default): kernel unit tests 1.53 vs 1.05 s (+45%), `kernel_fuzz` 0.26 vs 0.18 s (+44%), `kernel_soundness_fuzz` 0.46 vs 0.33 s (+39%), `compile_fuzz` 6.4 vs 5.2 s (+22%, mostly not kernel work). Small `church_bv` widths are mixed: n=8 faster (2.6-3.0 ms vs 3.5-7.1 ms), n=16 slower (17-19 vs 9-14 ms), n=32 faster (14-15 vs 26-36 ms). Every node construction pays a key rebuild and a table lookup, every node drop a second one, including the many short-lived temporaries `whnf` and `instantiate` make.
- **What does not disappear.** The generation stamp, `canonical_inputs` and `canon` become unnecessary, but the instantiate, shift and relevance memos are keyed by node pointer and keep their sources alive, so they still need a scope to bound their lifetime; `Scope` stays. The elegance gain is the node table and canonical flag only.
- **Verdict.** B works and gets A's large-proof gain with no API, but costs 20-45% on small kernel-bound workloads, rewrites two tests, adds a bound and a `Drop` to every `Rc`, and does not remove the scoped memos. A is kept as the design; B stays on the branch as a measured alternative. It would become attractive only if the always-on overhead were cut (for example by skipping the lookup for nodes known to be short-lived, which needs the callers to say so, which is A again).

## 71. `InternScope` on real proofs; n=512 profile with A; survey of the two non-sharing tests

- **Real `proof.rs` proofs** (`tests/proof_scope.rs`, ignored: gcd universal proof with 2 and 3 leaves, 200 builds and re-checks per measurement, interleaved scoped/unscoped, 3 rounds, CPU 44% at start): build 0.48-0.75 ms unscoped vs 0.69-1.36 ms scoped (gcd_2_leaves), 0.52-0.61 vs 0.79-0.85 ms (gcd_3_leaves); re-check 0.22-0.37 vs 0.11-0.17 ms (gcd_2_leaves), 0.24-0.27 vs 0.11-0.12 ms (gcd_3_leaves). So the scope halves the re-check and adds 0.2-0.3 ms to the build: **a net loss of about 20% on these small proofs** (total 0.7-1.1 ms unscoped vs 0.85-1.5 ms scoped). The proofs are tiny and the scope's table fills and empties for each; the scope pays only when the proof is large or is checked several times inside one scope. Guidance: hold an `InternScope` around large generated proofs, not around every build.
- **Profile, n=512, option A (14185 samples, whole scoped run to n=512; 10.0 s check, 1.7 s build at n=512):** `infer_node`/`check_rc` 72% inclusive; `shift_via` 21%; `hc::intern` 17% (hash probing; `::with::` self 16.6%, `find_inner` 16%); `def_eq` 13%; `whnf_step` 12.5%; non-app (allocator, page faults, `ntdll`) 24.6%. `canon` no longer appears.
- **The cache explanation for input memory is refuted.** With the proof 28x smaller (457k nodes, tables about 250 MB) the check still grows 6.2x from n=256 to n=512 (1.6 s to 10.0 s), against about 3.9x in counted work (section 67). The superlinearity is in the checker's own per-visit cost at depth: contexts reach 2n+2 = 1026 binders at n=512, and the three costs that scale with depth are the context-window id (`memo_context`, 3% self), the shifts of binder types on variable lookup (`shift_via` 21%) and the infer-memo key. Not yet separated; the next step would be counting per-lookup work against depth.
- **Survey: rewriting the two tests that fail under option B.** (1) `infer_memo_changes_no_answer` compares `infer` on a shared random term with `infer` on a deep copy built by `shift_ref`, asserting by `strong_count` that the copy shares nothing, so the memo (pointer-keyed) cannot engage on it. Under B the copy cannot exist. A rewrite needs a memo-free reference answer: a `#[cfg(test)]` switch on `InferCache` that disables the memo (about 5 lines), and the assertion becomes `infer` with the memo against `infer` without it on the same term. (2) `close_is_linear_in_the_dag_of_a_shared_body` asserts `dag_size == 3*DEPTH + 3` (93); under B it is 64 because more nodes merge. The test means "linear in the DAG, not the tree"; `<= 3*DEPTH + 3` states that and passes under both. Neither is needed for option A, which is the design on `main`; both are about 15 lines in total if B is ever kept.

## 72. Why the check still grows 6x per doubling: table lookups get slower with size

- **Not variable lookup.** Profile filtering of the n=512 scoped run (14185 samples): samples under `ctx_lookup` are 0.3%; the whole-check shift visits in `ctx_lookup` were already linear (1,150 / 2,302 / 4,606 at n=64/128/256). The 21% under `shift_via` is mostly the proof *builder* (`shift_memo` callers 27.5% of those samples, `shift_unchecked` 34%) and, inside it, table operations: the innermost frames are `hc::intern_as`, `hashbrown` probing and `NodeKey::eq` (about 40% together), not the shift walks. `memo_context` is bounded by a window of 8.
- **Table lookups are the superlinear term.** `table_lookup_cost_by_size` (ignored test in `church_bv.rs`; random hits in a `hashbrown` map with 24-byte keys and 16-byte values, 2M probes): 16k entries 8 ns, 64k 25 ns, 262k 47 ns, 1M 69 ns, 4M 140 ns. Our tables at n=256 hold about 0.2-0.35M entries each and at n=512 about 0.85-1.3M (section 67), i.e. about 47 ns vs about 70 ns per lookup, 1.5x. Counted work grows about 3.9x per doubling and per-visit cost 1.5-1.6x, which together give the observed 6.2x. The cache-bound hypothesis of section 67 is confirmed for the tables (not for the input, which section 71 refuted).
- **What would move it.** Each doubling of n multiplies the entries about 3.7x, so every lookup pays more. Levers, by what they remove: fewer entries (section 64 removed 99% of the instantiate entries; `uses` 0.84M and `shifts` 1.0M entries remain, plus 1.29M nodes), smaller entries (section 68: under 10% of footprint), or locality (a node-local cache of the last instantiate/shift result, so a repeat hit costs no table lookup). Not tried.

## 73. Measuring the three section-72 levers before building them: low value, one invalid profile

- **Table operation counts are small.** At n=512 scoped the whole check does about 2.5M `shift_get`, 2.1M `uses_get` and 0.87M `inst_get` calls. At 50-140 ns each that is 0.3-0.7 s of the 13-17 s check, so a node-local last-result cache (lever 1) or a merged table (lever 3) can save a fraction of that at best. Lever 2 (fewer entries) acts only through the per-lookup cost growth of section 72, which is the same bounded term. None is worth its complexity yet.
- **Rc-valued infer memo: no effect.** Storing the interned `Rc` in `InferCache.types` instead of an `Expr` copy changed nothing measurable; reverted.
- **Teardown is an unscoped-path cost.** Drop-ish self samples (`Rc` drop, `drop_inner_table`, `drop_elements`, dealloc) are 25.5% of the unscoped n=512 profile and 5.8-5.9% of the scoped one, so option A already removes it.
- **Invalid attempt.** Profiling scoped n=256 and n=512 separately failed: the `Samply` scheduled task does not inherit environment variables, so `ONLY_N` was ignored and both profiles covered all widths. The two runs also differed by load (n=512 check 17.4 s vs 23.4 s). Their per-function comparison says nothing about scaling and is not used. A per-width profile needs one test function per width (as `profile_add_zero_n128/256/512`), not an env switch.
- **Open.** What dominates the scoped n=512 check phase is still unexplained after the table counts; the last profile puts `infer_node` closures, `memo_context`, `infer_rc` and `hc::eq` at the top of the per-function growth.

## 74. Per-width scoped profiles: the excess growth is kernel time, not kernel-crate code

`profile_scoped_n256` and `profile_scoped_n512` (new, ignored; one test per width because the `Samply` task passes no environment) build and check inside one `InternScope`. Samples: 2,854 at n=256, 18,709 at n=512 (6.6x; wall 2.8 s to 19.4 s, with the profiler). `check_rc` is 80% / 70% of samples (the rest is the builder and teardown).

- **Per-function growth is uniform.** Under `check_rc`, `memo_context` 5.6x, `infer_rc` 5.6x, `infer_node` closure 5.9x, `whnf_step` closure 6.3x, `check_rc` closure 5.9x, `hc::intern_as` 5.1x, `hc::eq` 7.7x. No kernel-crate function is an outlier, and `memo_context` (suspected of a context-key cost) is not one. This matches counted work (about 3.9x) times the lookup-cost growth of section 72 (1.5x), i.e. about 5.9x.
- **The excess is `ntoskrnl.exe`.** Leaf frames outside the executable: 578 samples at n=256 (20% of all) and 5,015 at n=512 (27%), 8.7x, the biggest single grower (the `<non-app>` row is 8.5x). `ntdll`/`KernelBase`/`vcruntime` add under 3%. The kernel frames are unsymbolised (no kernel PDB); the heaviest (`0x6bfb9c`) is one site with 645 samples. The likely cause is page faults on fresh heap pages (peak 1.1 GB at n=512, section 69): faults grow with the memory touched, which grows about 3.7x per doubling in table entries plus the proof DAG, and zeroing/faulting a page costs more under a larger working set. Unverified: no page-fault count was taken.
- **Not contention.** Samples here are on-CPU; the run was at normal priority with Defender real-time protection off (checked in the preceding runs), and the n=512 time was 19.4 s in a run with a profiler attached.

Levers this suggests: a different allocator or a pre-sized arena (checks the page-fault hypothesis directly), and fewer fresh allocations (reuse). Neither tried; an allocator swap adds a dependency.

## 75. Page faults confirm section 74: re-faulting grows faster than memory

`profile_scoped_n256/512` run as plain processes (BelowNormal, the profiling exe from section 74), polling `Win32_PerfRawData_PerfProc_Process` for the cumulative page-fault count and peak working set. Defender real-time protection off; the machine was loaded by another session (total CPU 68-83% before launch), so wall times are inflated, but faults and the user/kernel split are counts and CPU times, not wall.

| | wall | user | kernel | page faults | peak WS | faults / peak pages (4 KB) |
|---|---|---|---|---|---|---|
| n=256 | 2.9 s | 1.97 s | 0.73 s | 144k | 322 MB | 1.8 |
| n=512 | 21.6 s | 10.8 s | 5.66 s | 1.37M | 1,119 MB | 4.8 |

- Faults grow 9.5x per doubling, memory 3.5x, kernel time 7.7x, user time 5.5x (the user figure matches section 74's per-function 5-6x). Kernel time is 27% of the n=256 CPU and 34% of the n=512 CPU, about 4 us per fault.
- At n=512 each page is faulted in about 5 times over the run, so most faults are not first touches: the heap is returning memory to the OS and taking it back (decommit and recommit), or the working set is being trimmed. A first-touch-only run would show about 1 fault per peak page.
- This supports section 74's hypothesis. It does not yet show the cause (the Windows heap's decommit policy vs working-set trimming under load); the next test is an allocator that keeps its memory (mimalloc, or a bump arena for nodes), expected to remove most of the 5.66 s kernel time.

## 76. The re-faulting is stacker segment churn, not the allocator (corrects section 75)

Section 75's next step (try mimalloc) was wrong: `tests/church_bv.rs` already sets mimalloc as its global allocator, so every profile and fault count above ran with it.

- **Allocator purge is not it.** `MIMALLOC_PURGE_DELAY=-1` (never return memory), alone and with `MIMALLOC_ARENA_EAGER_COMMIT=1`, left faults at 1.33M against 1.38M (n=512, interleaved, BelowNormal, machine 42-90% loaded).
- **Segment count.** A temporary counter in `grow_slow` (reverted) printed that `stacker::grow` allocated between 65,536 and 131,071 segments (1 MB each) during the n=512 scoped run: the recursion repeatedly crosses a segment boundary, and stacker allocates the segment on entry and frees it on return, with no reuse.
- **Larger segments are worse.** `STACK_PER_RECURSION` 16 MB: 1.55M faults, kernel 5.5-7.6 s; 64 MB: 2.67M faults, kernel 17.5-20.9 s (baseline 1 MB: 1.37M, 4.1-4.2 s). The per-segment cost scales with its size.
- **No segments, no churn.** `profile_scoped_n512_big_stack` runs the same check on a thread with a 1 GiB stack, so `grow` never switches. Interleaved against `profile_scoped_n512` in one exe:

| | wall | user | kernel | faults |
|---|---|---|---|---|
| default stack | 11.4 / 13.6 s | 7.9 / 8.5 s | 3.2 / 4.3 s | 1.37M / 1.41M |
| 1 GiB stack | 9.4 / 9.4 s | 7.1 / 7.3 s | 1.5 / 1.5 s | 406k / 408k |

  Wall time falls 18-31%, kernel time by more than half, and about 1M of the 1.37M faults go away. The 0.4M left is about 1.4 faults per peak page, i.e. first touch. (Defender real-time protection off; other sessions' load on the machine varied, hence the ranges and interleaving.)
- **Why n=512 and not n=256.** Deeper recursion crosses boundaries more often: n=256 took 144k faults in total, 1.8 per peak page.
- **Fix options, not yet built.** (a) Keep freed segments on a thread-local list and reuse them (the churn disappears at the cost of holding the memory); (b) hysteresis, so a boundary-straddling recursion does not alloc/free per crossing; (c) a large first stack for callers that can spawn a thread (a library API change, and it moves the cost to the caller). (a) is the least invasive; `stacker` has no hook for it, so it means replacing `stacker::grow` with our own segment switch (platform-specific, Windows fibers or inline assembly), so check (b) first.

## 77. Large checks run on one big stack segment (fixes section 76)

- **Is it a general tax? No.** A temporary counter (reverted) of `stacker::grow` segment switches per run: n=64 and n=128 none, n=256 about 11k, n=512 65k-131k, the gcd proofs none. Only very deep checks cross segment boundaries.
- **How stacker does it on Windows** (`stacker-0.1.25/src/backends/windows.rs`): `ConvertThreadToFiber` if needed, `CreateFiber(stack_size)`, `SwitchToFiber`, `DeleteFiber`, `ConvertFiberToThread`, per segment, with no reuse. That is why per-segment cost grew with segment size in section 76.
- **Why hysteresis cannot work with stacker.** The oscillation is at the boundary of the thread's own stack (1-2 MB deep), and a segment is gone when its call returns, so there is nothing to keep. A reusable segment pool would mean replacing `stacker::grow` with our own fiber switch (unsafe, Windows-specific); not needed, see below.
- **The change.** `check_in` runs its body inside one `on_segment(CHECK_SEGMENT = 64 MB, ...)` when the term and claim are large (`hc::large`: more than `LARGE` = 3000 distinct nodes, the bound that already triggers input interning; under `cfg(test)` always, so the unit tests exercise it). `grow_slow` and the new `on_segment` share the stacker call and the `FLOOR` bookkeeping. Experiment before the change: 64 MB, 512 MB and 1 GB behaved the same (reservation costs no RAM until touched; it does cost commit charge, 2026-10-23, PARKED.md "Large `check_in` segments that commit only what they touch"), faults 0.41M against 1.37M; a deeper recursion still chains ordinary 1 MB segments.
- **Result** (`profile_scoped_n512`, interleaved old/new exes, BelowNormal, Defender real-time protection off, machine CPU 21-33% before launch; 3 rounds): wall 11.3 / 14.8 / 13.1 s to 8.2 / 10.8 / 9.1 s (25-31% less), kernel 3.4-4.1 s to 1.2-1.7 s, page faults 1.36-1.40M to 0.40M. n=256, 128, 64 and the gcd proofs: no difference outside the noise (inputs under `LARGE` take the old path; n=256 faults 245k to 200k). All tests pass with and without the `hashcons` feature.
- **Still open.** About 0.4M first-touch faults remain (1.4 per peak page), and kernel time is still 1.1-1.7 s of 8 s; user time at n=512 (about 6.5-8 s) is the 5-6x per-doubling work of section 74.

## 78. What the scoped n=512 check spends now; threshold and scope questions

- **Profile after section 77** (`profile_scoped_n512`, 7,562 samples, 7.6 s): kernel (`ntoskrnl`) leaf samples fall from 27% to 7.5% of all samples. `check_rc` is 63% inclusive; `infer_rc` 66%; `def_eq` 12.7%; `whnf_step` 13.6%; `memo_context` 2.7%. The largest single block is the node table: `hc::intern` is 24% of all samples (`intern_new` 10.7% of it is the builder's constructors), `hc::uses` 4.8%, `shift_get` 4.8%, `inst_get` 1.7%. Inside `intern_as` the samples are the thread-local table access (21.5%, where the hashbrown probe and its cache misses land), `NodeKey::eq` on hits (13.8%, the key compare touching a cold entry) and the hash (about 10%). So the remaining superlinear cost is the memory-bound table lookups of section 72, now without the stack-segment tax; the levers there (fewer lookups, smaller keys) are the unbuilt ones.
- **Is the 3000-node threshold right?** Chains of nested `Pi` of depth 500/1000/2000/2900 (all under `LARGE`, so they take the old path), 20 checks each: 301 segment switches in total, about 4 per check at the deepest, 5 ms per check. A fiber per switch is tens of microseconds, so the cost is a few percent at most. A depth-based trigger is not needed; keep `LARGE`.
- **Should `InternScope` engage by itself?** It cannot for the builder: the proof is built before `check_in` is called, so only the caller knows whether the build is big. The checker side already is automatic (`canonical_inputs`). Left explicit; the rustdoc on `InternScope` now says when it pays (large proofs; about 20% loss on the gcd-sized ones).

## 79. Intern-call census, the re-measured curve, and a guard for the segment fix

- **Skipping no-op interns is moot.** A rebuilt node in `shift_child` (loose above the cutoff) or in `instantiate` (loose at or above the depth) always has at least one changed child, so "unchanged children, return the original" never applies. Counting `intern` calls by site at n=512 scoped (temporary counters, reverted): constructors and the rest 11.35M calls, 94.6% hits; `shift_child` 1.13M, 53% hits; `instantiate` 0.85M, 81% hits. The 10.7M builder hits are the 12.9M-node proof tree being built through a table that already holds 457k distinct nodes (about 0.8 s); they could only be cut by the builder caching its own repeated subterms, which is a property of this test's builder, not of the kernel. The check side is 2M calls, but the new-node ones (0.5M shifts, 0.16M instantiates) pay the allocation, table insert and growth, which is where its share goes.
- **The curve after section 77** (quiet machine, CPU 6% before launch, Defender real-time protection off, BelowNormal, `add_zero_lemma_scaling_scoped`, two scoped runs and one unscoped):

| n | scoped build | scoped check | unscoped check | proof DAG scoped / unscoped |
|---|---|---|---|---|
| 64 | 15-17 ms | 51-61 ms | 112 ms | 14k / 288k |
| 128 | 53-60 ms | 221-248 ms | 487 ms | 41k / 954k |
| 256 | 229-230 ms | 1.02-1.05 s | 2.17 s | 130k / 3.4M |
| 512 | 1.05-1.17 s | 4.8-5.1 s | 9.1 s | 458k / 12.9M |

  Scoped check per doubling: 4.3x, 4.4x, 4.7x (was 6.2x at 256 to 512 before sections 74-77; the counted work is about 3.9x, the rest is the table-lookup growth of section 72). The n=512 check is 4.8-5.1 s against 13-17 s at the start of this thread's measurement (13 s with the other session's load, section 69), and 25 s unscoped before section 77.
- **Guard.** `a_large_check_does_not_churn_stack_segments` (ignored; n=256, release) asserts under 100 stack segment switches in one check, read from the new `kernel::segment_switches()` (a thread-local counter in `on_segment`, on the cold path). It reads 1 with the fix and 11,198 with `check_in`'s big-segment call disabled, where it fails.

## 80. Real-proof sharing, a negative result on table growth, and where the performance thread stands

- **Real proofs repeat themselves modestly.** `real_proofs_dag_against_tree_size` (ignored, `tests/proof_scope.rs`): tree nodes against distinct allocations for the universal proofs, unscoped and built in an `InternScope`:

| proof | tree | distinct unscoped | distinct scoped |
|---|---|---|---|
| factorial | 1,266 | 419 (3.0x) | 192 (6.6x) |
| fib | 3,202 | 672 (4.8x) | 308 (10.4x) |
| gcd | 1,522 | 521 (2.9x) | 229 (6.6x) |
| gcd, 3 leaves | 2,709 | 744 (3.6x) | 308 (8.8x) |

  Against 28x for the n=512 lemma, and all under 3,300 nodes in the tree. Builder-side caching of repeated subterms (section 79, 10% of the n=512 samples) would buy nothing for these; it is a property of the Church-bit-vector builder, not of the kernel. Not pursued.
- **Growing the node tables four-fold instead of two-fold: no effect.** `reserve_rehash` is 14.1% of the n=512 scoped samples (68% of it from the `hc` tables). A helper that grew each full `hc` table (nodes, instantiate, shift, relevance) to four times its size once past 16k entries was interleaved against the committed build (4 rounds at n=512, 3 at n=256, machine CPU about 50%): n=512 user time 8.2 against 8.3 s on average, n=256 no difference; peak working set +2%. The rehash samples are the cost of re-inserting entries whose keys are cold in cache, which fewer rehashes at four-fold growth do not remove (each entry is still moved about once); reverted.
- **Where the thread stands.** The n=512 lemma check went from about 25 s (unscoped, start of this thread) to about 9 s unscoped and 5 s scoped, with 4.3-4.7x per doubling, close to the counted work. What is left is memory-bound table traffic (sections 72, 78, 79) with no cheap lever found among: node-local caches (op counts too small, section 73), merged tables, no-op skipping (impossible, section 79), pre-sizing (section 68) and four-fold growth. Sections 67 and 69-72 explain the n=256 to n=512 growth by `shift_via` and `memo_context` depth costs and by table cache misses; sections 74-77 supersede the larger part of that (the kernel/page-fault cost of stack segments).
- **Natural next work** is on the bit-vector program, not the checker: section 27's commutativity timings (n=8 to 32, taken on a machine 87% busy before any of sections 62-77) are stale and its n=64 point was never run; with the checks now 2-4x faster it may be reachable.

## 81. Commutativity re-timed: 300x faster, and reachable to n=1024

`add_comm_scaling_scoped` (new, ignored, `tests/church_bv.rs`; widths from `COMM_NS`, `NO_SCOPE` for the control) builds and checks `add x y = add y x` (section 27) inside one `InternScope`. Release, mimalloc, BelowNormal, machine CPU 16% before launch, Defender real-time protection off; peak memory from the process:

| n | scoped build | scoped check | unscoped check | proof DAG scoped / unscoped |
|---|---|---|---|---|
| 8 | 1.4 ms | 1.7 ms | 5.5 ms | 1.3k / 19.6k |
| 16 | 1.9 ms | 5.0 ms | 7.4 ms | 2.4k / 37k |
| 32 | 4.4 ms | 13.7 ms | 28 ms | 5.2k / 75k |
| 64 | 11 ms | 30 ms | 64 ms | 13k / 159k |
| 128 | 27 ms | 105 ms | 220 ms | 38k / 363k |
| 256 | 81 ms | 446 ms | 770 ms | 126k / 921k |
| 512 | 422 ms | 1.94 s | not run | 448k |
| 1024 | 2.18 s | 10.9 s | not run | 1.68M |

Peak working set 0.57 GB at n=512 (scoped, three widths in one process) and 1.73 GB at n=1024. Section 27 had n=32 at 8.5 s on a machine 87% busy and n=64 extrapolated to 70-120 s: n=32 is now 14 ms scoped (28 ms unscoped) and n=64 30 ms, about 300x faster at n=32, and the n=64 point that was never run is trivial. The per-doubling check ratio is 3.5x at 128 to 256, 4.3x at 256 to 512 and 5.6x at 512 to 1024 (the n=1024 point is likely table-lookup growth, section 72). Both proofs (the lemma of section 18 and this one) use the same machinery, so the speed-up is the sum of sections 41-77, not any single change. The statement-must-fail checks (`add x y = add x x`) still run only at n=1, 2, 4 in `add_is_commutative_on_symbolic_good_vectors`; the large widths here only show that the proof checks.

## 82. What `n` is, and rejecting a false statement is exponential in `n`

- **`n` is the bit width of the vector type.** `Bv_n` (`bv_ty(n)` in `tests/church_bv.rs`) is the Church tuple `Pi C:Sort1. (Bool -> ... -> Bool -> C) -> C` with `n` Boolean arguments, least significant bit first; the unrolled `add` has `n` bit positions with a ripple carry. Real machine words are `n` = 32 and 64 (`Bv32`, `Bv64`, section 2). So the n=512 and n=1024 rows of sections 79-81 are scaling stress of the checker (term size and context depth grow with `n`), not widths the compiler uses; n=32 and n=64 are the ones that matter, and every proof here is stated and checked at one fixed `n` (a generator builds the `n`-position proof; there is no single proof for all `n`).
- **Rejection blows up where acceptance does not.** The commutativity proof for `add x y = add y x` checks in 30 ms at n=64 (section 81), but the mutation checks of `add_is_commutative_on_symbolic_good_vectors` (`add x y = add x x`, against its own proof and against the right proof) are exponential in `n`. `add_comm_rejection_probe` (new, ignored; `COMM_N`, `COMM_CASE`=`own`|`right`; run under a watchdog), scoped, release:

| n | own proof | right proof | peak memory |
|---|---|---|---|
| 4 | 2.1 ms | 2.0 ms | 10 MB |
| 6 | 7.1 ms | 5.4 ms | |
| 8 | 56 ms | 46 ms | |
| 10 | 0.75 s | 0.70 s | 0.2 GB |
| 12 | 11.1 s | 11.1 s | 2.4 GB |

  About 3.7x per bit (13-15x per two bits). A first attempt at n=32 and 64 tried a 75 GB allocation and aborted (`STATUS_STACK_BUFFER_OVERRUN` from the allocation failure). So false statements are rejected correctly at small `n` and are not reachable at 32 or 64 on this kernel. (The `add_comm_rejects_the_wrong_statement_at_real_widths` test written for this was removed.)
- **Likely cause, not yet confirmed.** When `def_eq` fails it has no equality to stop at, so conversion normalises both sides; the symbolic carry at position `i` mentions the carry at `i-1` three times (`or(and(a,b), and(c, xor(a,b)))` with `xor` unfolding to two more), so the normal form is a tree of size exponential in `n` even though the term is a linear-size DAG. Acceptance never builds that normal form because the proof's congruence steps meet the two sides at matching shapes. This is the same exponential tree against linear DAG behind section 19's n^3 and section 37's finding, now seen on the failure path.
- **What it costs.** Not a soundness problem (a wrong statement is still rejected, eventually), but it means the mutation tests cannot run at real widths, and a wrong proof or statement at 32 or 64 bits would hang or exhaust memory instead of reporting an error. Remedies, by what they change: a node or time budget on `def_eq` that reports "unknown" (turns the hang into an error), a shared (DAG-preserving) normal form so failure costs about what success does, or stating the obligations over `add_shared` (section 28's let-bound carries).

## 83. Correction to section 82: the rejection cost was formatting the error, not conversion

- **Profile of the n=11 rejection** (samples inside the test thread, 2,673): 99.6% inclusive in `core::fmt` (`Formatter::write_fmt`, `Debug for Expr`), 85% in `alloc::fmt::format`; `def_eq`, `nf`, `whnf_step`, `instantiate_n` and `intern` together under 1%. The checker finds the mismatch quickly. It then builds the error text, `"type mismatch: inferred {:?}, expected {:?}"` of `nf(inferred)` and `nf(expected)`, and a `Debug` of a term prints its tree, which for the carry chain is exponential in the DAG (the earlier 75 GB request was that `String`). Section 82's "normalises both sides" explanation was wrong.
- **Fix, once, at the shared point.** `kernel::brief` prints `{:?}` through a writer that fails after 400 characters (the failed `write!` unwinds the printer, so the work is bounded too) and appends ` ...`. All eleven non-test error sites that printed an `Expr` use it (`type mismatch`, `expected a Sort/Pi/W/Sigma`, `lambda domain mismatch`, the `sup` and `wrec` mismatches, a constant's open type). The debug-only composition-bug panic in `proof.rs` still prints the full term.
- **Result** (`add_comm_rejection_probe`, scoped, release, watchdog; machine quiet): rejecting `add x y = add x x`, own proof / right proof:

| n | before | after |
|---|---|---|
| 8 | 56 / 46 ms | 5.1 / 2.8 ms |
| 12 | 11.1 / 11.1 s, 2.4 GB | 11 / 5.5 ms, no memory |
| 16 | not run (about 3 min) | 22 / 7.6 ms |
| 32 | aborted on a 75 GB allocation | 77 / 44 ms |
| 64 | aborted | 419 / 174 ms, 0.18 GB |

  The mutation checks now run at the real widths. Guards: `kernel::tests::brief_bounds_the_text_of_an_exponential_tree` (a DAG of 2^60 tree nodes prints in under 100 ms), and `add_is_commutative_on_symbolic_good_vectors` now includes n=16 (0.7 s in a debug build; it took minutes before).
- **The general lesson, and which earlier fixes it joins.** The same shape (a DAG that is linear but is walked or printed as a tree) has now been fixed case by case at: the proof builder (`cong_n` and `trans_proof` shifts, sections 55-56, generalised by `InternScope`, section 69), the checker's `instantiate`/`shift`/relevance memos (sections 51, 60, 64, generalised into the one node table), the `Debug` printer (this section), and the stack (section 77, a different cost but the same "a deep recursion paid at every crossing"). Remaining tree-recursive walkers over `Expr` with no pointer memo, found by listing the functions that call `grow`: `is_var_free` (pruned only by the cached loose range, so a DAG whose variable is absent but whose range is high is walked as a tree), `Expr::eq` (short-circuits on pointer equality and on canonical nodes, otherwise structural), and the test-only `*_ref` walkers. Not measured; an audit would time each on the carry-chain DAG at n=64.

## 84. Audit of the remaining tree-recursive walkers: exponential on adversarial DAGs, absent from real workloads

- **Probe** (temporary unit test, reverted; release): a DAG `e_{i+1} = App(e_i, e_i)` over `Var(5)` (tree size 2^k, loose range 6, so the range cannot prune). `is_var_free(e, 0)` for the absent variable: 1.2 / 3.0 / 11.8 / 49.9 ms at k = 16 / 18 / 20 / 22. `==` on two structurally equal DAGs built separately (no shared nodes between them, not canonical): 0.28 / 1.2 / 4.6 / 18.6 ms. Both double per level, i.e. they walk the tree. `Expr::eq` short-circuits on pointer equality and on two canonical nodes only; `is_var_free` has no memo at all. `is_var_free` is called from `whnf_step`'s `WRec` case (`(0..k).any(|i| is_var_free(arg, i))`, one walk per `i`) and from the `Sup` arm of `infer`.
- **Not on the real workloads.** Fresh profiles with symbols matching the executable (n=512 lemma, scoped 7,030 samples, unscoped 13,889): `is_var_free` 0 samples in both; `eq_noting` 0.5% / 0.3%; `same_shape` (which `==` and `conv_whnf` share) 4.7% / 2.6%. (An earlier reading of 70% for `is_var_free` was a symbol mismatch: the profiling exe had been rebuilt after the profile was recorded. Profiles must be read against the exe they came from; `church_bv_prof.exe` and its PDB are overwritten by each new build.)
- **Decision: record, do not fix.** No workload hits them, a visited-set in each costs time on the small terms that dominate, and a fix would be a guess at a trigger. If one appears, the fix is a visited set that switches on after a visit threshold (as `WARM_UP` does for the node table), keyed by (pointer, index) for `is_var_free` and by (pointer, pointer) for `==`.
- **Error paths elsewhere.** `proof.rs`, `jit.rs` and `kernel_lazy.rs` print no kernel terms in production errors: `proof.rs` discards the kernel's error with `.ok()?` at its re-check sites (so the message was being built and thrown away; now at most about 400 characters). The one full-term print left is the debug-only composition-bug panic in `proof.rs`, and the asserts on closed postulate types in `kernel.rs`, both panic paths.

## 85. D3 (`wrapping_div MIN (-1) = MIN`) proved; `div_s` is abstract; future goal: search blended with execution

**D3 done** (`tests/church_bv.rs`: `eq_bv`, `wrap_div`, `wrap_div_min_proof`, tests `eq_bv_computes_on_literals`, `wrapping_div_min_by_minus_one_is_min`). Checked at n=1,2,4,8,32,64 in 0.2 ms .. 52 ms (n=32) .. 282 ms (n=64), scoped; CPU load about 6%, Defender real-time protection off.

Assumptions and what the proof shows:
- `div_s` is not in the library, so its raw result `r = div_s a b` is a variable with a `GoodBv` witness. The statement is `Pi r. GoodBv r -> Id(Bv_n, wrap_div(a, b, r), MIN)` with `a = MIN`, `b = -1`.
- A Church `Bool0` lives in Sort1 and cannot select between `Bv` values (its eliminator targets Sort0), so the wrapper muxes bitwise with `or(and(c, x), and(not c, y))`. A selection at `Bv` level would need a higher-universe Bool or a `GoodBool` motive.
- The guard is `and(eq a MIN, eq b -1)` with `eq_bv` a generated Church term; it reduces to `true` by conversion on literals, so the step case is `refl MIN`. `GoodBv` is needed because conversion does not eta-expand a neutral `r` (`r C (_i. ..)` does not reduce).
- Mutations are rejected: `(MIN, -2)`, `(MIN+1, -1)`, `(0, -1)`, `(MIN, 0)`.

Not done: D1/D2 (`None` iff `b = 0` or the overflow case; `Some (wrapping_div ..)` otherwise). They need a Church `Option` with None/Some disjointness and a spec for `div_s`; `b = 0` also needs `eq_bv` completeness for good vectors (H3), which wants `toN` (H1).

### Future goal (from the user, 2026-10-01; tentative, nothing started)
With lemmas ablated from the library, AI proof search should be able to rediscover the missing ones. Search should run concurrently with execution and use insights from execution. Explore how far the phases can be blended; `../renno` is a source of ideas.

What `renno` offers (read from its README and docs layout, not yet studied in code):
- **Gradual verification**: a refinement `n: Int where 0 < n` is proven outright when cheap, otherwise checked at run time. The same three-way shape (proved statically / checked dynamically / unknown) applies to a lemma: a conjecture can be run against concrete values first, and only conjectures that survive are sent to the kernel.
- **Multi-shot algebraic effects**: a captured continuation can be resumed zero, one or many times, which is the natural substrate for proof search as an effect (`choose`/`fail`) over a running program, with execution state shared across branches.
- **Execution observations as search hints**: values seen at run time (for example the `x + 0` shape in `add x 0`) suggest the lemma statements to try; counterexamples prune them before any proof is built.

Open questions before design: (1) what an "ablation" is (drop one lemma from the library and require the search to reach the downstream theorem), and how success is scored; (2) whether the search runs inside the kernel's `InternScope` so candidate proofs share nodes; (3) how a lemma candidate is represented (statement only, with the generator-built proof shapes of this file as templates, vs. free-form terms).

## 86. `toN` (H1) design: universe obstruction and the lift; `Option` as flag plus payload

**Finding: no cumulativity.** The kernel does not let a Sort1 type stand where Sort2 is expected (`type mismatch: inferred Type1, expected Type2`), and a Church `Bool0` eliminates only into Sort0. So:
- A bit cannot be turned into a number by applying it (`Nat` is Sort1, `Bool0`'s motive slot is Sort0). Only the `GoodBool` eliminator (motive into Sort1) can, so `toN` takes a `GoodBv` witness.
- `GoodBv`'s motive is `Bv_n -> Sort2` (needed for `Id` statements over `Bv_n`), but `toN`'s motive is `Bv_n -> Nat`, a Sort1 value. Rejected as above.

**Fix: a generic lift, no per-operation doubling.** `GoodBv1 x := Pi P:(Bv_n -> Sort1). step -> P x`, and a closed term `lift_good : Pi x. GoodBv x -> GoodBv1 x`: eliminate the Sort2 witness into `GoodBv1` itself (a Sort2 type), with step `\a.. ga.. P s. s a.. ga..`. Then `toN x g := (lift_good x g) (\_. Nat) (\a.. ga.. . sum_i (ga_i (\_. Nat) 2^i 0))`. Tests: `to_n_computes_on_good_literals` (n=1,4,8: types check; `toN (lit v) (good_lit v) = v`, and `v+1` is rejected).

Options considered for the numeric view:
| option | pros | cons |
|---|---|---|
| A. `toN` over `GoodBv` via the lift (chosen) | no change to `Bv`/`Bool0`; computes on literals; one generic lift | `toN x g` mentions the witness `g`; each homomorphism needs a `GoodBv` preservation lemma per operation (`good_add`, ..) and a `Nat` library (`mod`, `pow`, `div`) that does not exist yet; proof irrelevance of `g` is not provable (statements quantify over `g`) |
| B. Raise bits to `Bool1` (`Pi C:Sort1`), `Bv` at Sort2/3 | `toN` is a plain function, no witness | rebuilds every helper and proof in this file at a new universe; `Nat` would still need to sit at Sort1 for `Bv`'s `C`; does not remove `GoodBool` (variables still need case analysis) |
| C. No `Nat`: state laws as `Bv` equations (comm, assoc, `add x 0`) | nothing new | cannot express `/`, `mod`, comparison against numbers, the allocator's distance condition |
| D. Kernel `Bool`/`Nat` (W types) in place of Church | strong elimination | a full re-encoding of the library |

**H3 (`eq a b = true -> a = b`)** does not need `toN`: it is a per-bit chain (`and x y = true -> x = true` and `y = true`, then `GoodBool` cases, then `cong_n`), the same shape as `add x 0 = x`. So H3 can be proved before the `Nat` library exists; the earlier note that it "wants `toN`" in section 85 was too strong.

**`Option` for division.** A Church `Option A := Pi R. R -> (A -> R) -> R` cannot be chosen by a `Bool0` condition for the same universe reason, so the library models `sdiv a b` as the pair (`sdiv_some a b : Bool0`, `wrap_div a b (div_s a b) : Bv`). `sdiv_some` is `not (eq b 0 or (eq a MIN and eq b -1))`. Test `sdiv_flag_matches_the_spec_on_literals`: for n=4,8,32,64 and 8 sample values per operand (all 64 pairs), the flag computes to the spec (`false` exactly for `b = 0` and `a = MIN, b = -1`), and not to its negation. D1/D2 for symbolic `a`, `b` are still open: they need H3 (flag false iff the guard holds, for good vectors).

Next: H3 forward direction (`eq a lit = true -> a = lit`, generator-built), then D1/D2 universally; then the `Nat` library for the `toN` homomorphisms, starting with `lt_u`/`add`.

## 87. H3 (forward), D1 (guard => None), D2 (payload), `good_add`; `true = false` is not refutable in Church `Bool0`

All in `tests/church_bv.rs`, scoped, n=1,2,4,8,32, mutations rejected. CPU load about 10%, Defender real-time protection off.

**Proved**
- **H3 forward** (`eq_lit_sound`): `Pi x. GoodBv x -> Id(Bool0, eq_bv x L, true) -> Id(Bv_n, x, L)` for a literal `L`. Peel the `and` chain with `and_peel` (left/right), recover each bit with `bit_from_xnor l`, then `cong_n`. n=32 checks in 8.8 ms. The goodness of each chain prefix comes from `good2`/`good_xnor_lit`.
- **D1, guard => None** (`sdiv_none_if_zero`, `sdiv_none_on_overflow`): `b = 0` gives `sdiv_some a b = false`, and `a = MIN, b = -1` gives the same, by `cong1`/`cong_n` and computation. No goodness needed.
- **D2, payload** (`wrap_div_keeps_r`): with the guard false, `wrap_div a b r = r` for `GoodBv r`. 10 ms at n=32.
- **`good_add`** (`good_add`, `good2`): `GoodBv x -> GoodBv y -> GoodBv (add x y)`, the witness `toN (add x y)` needs. 12 ms at n=32. `good2` is generic over a bit operation's truth table; and, or, xor instances are tested and a wrong table is rejected.

**Findings (each cost a failed attempt)**
1. **No eta in conversion shows up as a recurring gap.** `and true y` normalises to `fun C a b => y C a b`, not `y`; the same for `mux false m r_i`. Bit-by-bit fixes: eliminate the second witness too (`good_and`), or prove `x = eta x` by cases and chain it (`wrap_div_keeps_r`).
2. **Universe of the claim bounds what a witness may eliminate into.** `GoodBool` eliminates into Sort1, `GoodBv` into Sort2. A claim `Good (op c y)` is Sort2, and `GoodBv (add x y)` is Sort3, so neither can be a motive. The pattern that works: take the claim's own `P` as a parameter and apply the witnesses to `P (op c' y')` (`good_and_lemma`, `good2`, `good_add`).
3. **`true = false` cannot be refuted in Church `Bool0`.** A refutation needs a type family that differs on `true`/`false`, which needs eliminating a `Bool0` into a non-trivial type, but `Bool0` eliminates only into Sort0 and section 12 found no closed type at Sort0. So every proof so far avoids absurd cases (symmetry or identical hypotheses made the bad cases come out right). It blocks:
   - **D1 forward** (`sdiv_some a b = false` implies `b = 0` or overflow): the case where the guard is false yields `true = false`.
   - **H3 reverse as a disjunction** and the `None`/`Some` disjointness obligation of section 6.
   - Any "if and only if" that needs a case to be impossible.

   Options: (a) postulate `Id(Bool0, true, false) -> Empty` (a trusted axiom, sound in the standard model but it enlarges the trusted base); (b) carry the observable Booleans as the kernel's W-type `Bool` (section 12 built it) with a conversion from Church bits, which `Bool0` cannot provide for the same reason, so the conversion would be part of the circuit's interface; (c) keep obligations to the provable directions: guard => None, payload, and `eq a L = true => a = L`, plus decidable checks on literals. The code now follows (c).

**`toN` homomorphisms** (step 3 of the plan) are not started. What they need, now known: `good_add` (done); a `Nat` library on Church `Nat` at Sort0 (`mod`, `pow`, `div`, and an induction witness per number, as in `church_encoding.rs`); statements using the specific witness `good_add x y gx gy`, because `toN` depends on the witness and two witnesses of one vector are not provably equal (no parametricity). Per-bit lemma for the sum: `toN (mk s) = sum_i s_i 2^i` with `s_i = x_i xor y_i xor c_i`, so the modular statement needs an induction over the carry chain.

Next: decide the `true = false` option, then the `Nat` library, starting with `toN (or a b) = toN a + toN b` for disjoint bit ranges (H4), which needs no `mod`.

## 88. Decision: option (c) for `true = false` (2026-10-01)

Chosen by the user: keep obligations to the directions provable without refuting `true = false` in Church `Bool0`. No axiom is added and the trusted base is unchanged.

In scope: guard => None (D1 reverse), payload (D2), `eq x L = true => x = L` (H3 forward), goodness preservation, and decidable checks on literals (`sdiv_flag_matches_the_spec_on_literals`).

Out of scope until a consumer needs it: D1 forward (None => guard), None/Some disjointness, H3 as a disjunction. Revisit (a) or (b) of section 87 then; the cost of reopening is one postulate or an interface change, not a rework of the proofs above, since none of them uses the missing fact.

Section 6 obligations affected: D1 is stated as "guard => None" plus the literal checks; any later obligation that quotes "iff" must be restated one-directionally or wait for this decision to be reopened.

## 89. Width scaling of �87's proofs; H4 by conversion; the unary `Nat` does not reach 32 bits

CPU load 10-24%, Defender real-time protection off; scoped; ms (check).

| n | H3 `eq_lit_sound` | D2 `wrap_div_keeps_r` | `good_add` |
|---|---|---|---|
| 32 | 9.2 | 13.4 | 17.7 |
| 64 | 14.5 | 26.7 | 90.2 |
| 128 | 118.9 | 120.5 | 305.8 |

At most 8x per doubling (`good_add` 64 to 128: 3.4x; H3 64 to 128: 8.2x, the worst). Test `bv_lemma_scaling_h3_d2_good_add` (ignored).

**H4 proved, by conversion alone** (`or_disjoint_proof`, test `or_of_disjoint_vectors_adds_in_to_n`): for `a` with free low bits `0..k` and `b` with free high bits `k..n` (other bits literally false), `toN (or a b) = toN a + toN b` is `refl` for every split `k` at n=2,4,8, each with its canonical witness (`good_tuple`, `good_or_bv`, built with the new generic `good_vec`, which `good_add` now also uses). The eta gap of �87 did not arise, because the zero terms are closed. `toN a + toN a` is rejected. This is the disjoint-range form: it covers structurally disjoint operands, not a symbolic "disjoint" hypothesis.

**Finding: the Church `Nat` of `toN` is unary, so it does not scale.** `to_n` weights bit `i` with `nat_lit(2^i)`, a numeral with 2^i nested applications. H4's check time by width: n=6: 2.5 ms, 8: 2.4, 10: 3.2, 12: 7.4, 14: 18.7 (about 2.5x per +2 bits); n=16 had not finished after 10 minutes, and 2^31 applications at n=32 cannot even be built. The proofs of �87 are unaffected (no `Nat`). This changes the plan for H1:
- Computing `toN` by conversion, and any statement that normalises a numeral, is limited to about n=14.
- A symbolic statement could keep the weights as shared doubling terms (`(fun x => add x x)^i one`) so that equal weights are compared by pointer, but a closed 32-bit value would still normalise to billions of applications.
- A numeral that scales is binary: the number as a `Bv` of its own bits (so `toN` is the identity and arithmetic is circuits), or a Church list of bits with a binary `add`. Statements about `mod 2^n` then become statements about vectors, and `lt_u`/distance conditions become circuits plus lemmas.

Recommendation: do not build the unary `Nat` library for H1. State H1 over circuits (`add` against a reference, `lt_u` as a circuit) and keep `toN` only as a small-width (n up to 14) cross-check.

## 90. H1 direction: laws over circuits (2026-10-01)

Taken from the recommendation of section 89 (the reply "1" did not name another option; reopen if it was meant to). Obligations that section 6 states through `toN` are restated over circuits, with no unary `Nat` library:
- `add`, `sub`, `mul`: laws against a reference circuit or each other (commutativity is proved, section 81; `add x 0 = x` is proved; associativity and `sub x x = 0` next).
- `lt_u`, `gt_u`, `le_u`: defined as circuits (borrow chain), with lemmas such as `lt_u x x = false` and transitivity on literals-plus-symbolic patterns as consumers need them.
- Anything with a numeric distance (the allocator's "at least 8 apart"): a circuit over `Bv`, e.g. `lt_u (sub b a) 8`, rather than arithmetic on `Nat`.
- `toN` stays as a small-width (n up to 14) cross-check only (`to_n_computes_on_good_literals`, H4).

Consumers decide the next lemma; no speculative circuit library.
