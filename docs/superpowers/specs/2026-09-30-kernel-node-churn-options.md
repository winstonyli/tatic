---
status: "superseded-by: docs/superpowers/specs/2026-10-02-search-execution-blend-design-part2.md"
---

# Cutting the node churn in kernel reduction: options (2026-09-30)

**Superseded (2026-10-04): the premise is out of date.** The n^3 growth and 19 s at n=64 below predate sections 51-81 of the bit-vector note (relevance-keyed infer memo, shared shifts in the proof builder, hash-consing, scoped interning). The `add x 0 = x` lemma now checks in about 0.13 s at n=64 (section 90b of the research notes, `shared_carry_scaling`), so none of the options here is needed for that lemma. Read this note as history.

Status: a design note for a decision, not a plan. Nothing here is built. It
answers: the profile (bitvector design doc, sections 20 and 21) says the
universal `add x 0 = x` lemma spends its time allocating and freeing `Expr`
nodes; what could change that, and what should be tried first?

## 1. Evidence, and what it does not show

Release build, mimalloc, lemma at n=64: 19 s, growth about n^3. Before
mimalloc (system heap): `drop_glue<Expr>` 35% inclusive, freeing the
per-call caches 25%, `infer_rc` lookups 14% self, `instantiate` 8% self.
Counters (section 19): betas grow about n^2, but `instantiate` entries grow
faster, so each beta touches a body that grows with n.

Not shown: that a lazy scheme would remove the n^3. The argument is an
inference from the profile and the counters. A re-profile with mimalloc (the
drop share may now be smaller) is the next measurement, before any kernel
design work.

## 2. What other kernels do (fetched 2026-09-30; see RELATED_WORK section 77)

- **Lean 4 kernel** substitutes eagerly. `instantiate` skips subterms by
  their loose-bvar range and runs through `replace_rec_fn`, whose cache key is
  (node pointer, offset), used only for nodes likely shared, per call. That is
  what the `instantiate` memo tried here (section 20), and it was slower on
  this lemma. Lean needs no lazy scheme for its workloads, so eager
  substitution is not inherently the problem; this lemma's term shape
  (O(n^2)-node bodies under O(n) betas) may be.
- **Rocq kernel** (`CClosure`) is lazy: a closure `FCLOS of constr * usubs`
  pairs a term with its substitution, `FLambda` keeps the body unevaluated
  under its environment, and `Zupdate` shares an evaluated result.
- **Compiled strong reduction** (Gregoire and Leroy, ICFP 2002; Kleeblatt's
  strongly normalizing STG machine, 2011): compile to an abstract machine that
  weakly reduces open terms, then read back a normal form. Reported "important
  speed-ups" over Coq's earlier interpreter-based reducer (abstract-level
  reading only).
- **Normalisation by evaluation** (Abel, Coquand and Dybjer, LICS 2007):
  environment-based evaluation into semantic values, then read back (search
  summary only).

## 3. Options

| | What changes | Pros | Cons |
|---|---|---|---|
| **S. Stay eager, shrink what it builds** | nothing in `kernel.rs`; change how the proof terms are generated (for example fewer or smaller carry bodies) | no trusted-code change; testable now | may only move the constant; the Church `add` body is inherently O(n^2) |
| **C. Retain less in the caches** | `whnf`/`nf` caches skip single-use results | small; attacks the cache teardown (25% before mimalloc) | may lose sharing the caches exist for; gain unknown after mimalloc |
| **L1. Closure-based whnf (Rocq style)** | `whnf` works on (term, environment) pairs, updates shared results, reads back an `Expr` for `infer` and `conv` | removes per-beta body construction; proven design | new value type, interior mutability for update, every reduction rule (`J`, `WRec`, `SigRec`) redone on closures; trusted core grows |
| **L2. NbE (semantic values)** | evaluate to a value type, compare values directly, read back only for output | clean theory, fast conversion | largest rewrite; `Expr` stays only at the boundary; most to audit |
| **G. Use the JIT to normalise (compiled strong reduction)** | normalise by compiling terms | fastest in the literature | puts the JIT into the trusted checking path (today its output is re-verified by the kernel, so it is untrusted); a second compiler for open terms plus read-back. Not chosen, and not ruled out: it fits the Wasm-target goal, so the trust trade-off is the owner's call. Variants not evaluated: use it only as an untrusted hint the kernel confirms cheaply, or sample-check it against the kernel as `verify` does for programs (sampling is not a soundness proof) |
| **B. Per-call arena** | bump-allocate nodes, free at once | kills drop cost | `Rc` everywhere (`Node`, `Drop` guard, `PtrKey`, tests); escaping terms need copying |

## 4. Recommendation and gate

1. Re-profile with mimalloc. If `drop`/cache-teardown is now under about 15%,
   stop: the exponent stays n^3 but the lemma is fast enough at n up to 32.
2. Try **C** (one small kernel edit, A/B measured). Keep only if the lemma
   at n=32 and 64 is faster and the proof benchmarks do not regress.
3. Only if the n^3 still blocks real work (for example a real-carry lemma at
   n=64), design **L1** in detail. It has the most precedent (Rocq) for a
   kernel that must stay a small core.

Any kernel change here is accepted only if: the new `whnf`/`nf`/`conv` agree
with the current ones on the random-term reference tests and the fuzz
targets; a mutation check shows the agreement test fails when a rule is
broken; and an A/B run (same profile, allocator, load and Defender state
logged) shows the lemma faster without a proof-benchmark regression.

## 5. Open questions

- Does `Zupdate`-style sharing need `RefCell`, and how does it interact with
  the pointer-keyed `ReductionCache`/`InferCache`?
- How are `Free` and `Const` handled in a closure (they are closed)?
- Should `conv` compare closures directly (NbE style) or read back first?

## 6. L1 and L2 in detail (added 2026-09-30)

**L1 (Rocq style).** Keep `Expr` as syntax and as the kernel's interface. Only
`whnf`, `nf` and `conv` change: they work on closures `(term, env)` where `env`
holds lazily evaluated, shared cells. Beta pushes the argument cell onto the
environment instead of substituting; a variable lookup forces its cell once and
updates it in place (Rocq's `Zupdate`). A closure is turned back into an `Expr`
only where the checker needs a shape (`expect_pi`, `expect_w`, `expect_sigma`,
error messages), and that read-back substitutes eagerly. So `infer`'s own
`subst_top` stays.

**L2 (NbE).** The whole checker runs on semantic values: types are values,
the context holds values, `infer` returns a value, `check` compares values with
de Bruijn levels for neutrals, and `Expr` is only the input and output syntax
(elaboration-zoo, smalltt and the Pie tutorial are built this way).

**What each can reach.** In the release profile on the system heap, 34% of
samples had a substitution frame (`instantiate`, `shift` or `subst_top`) on
the stack: 25% under `whnf`, 9% outside it (`infer`'s own `subst_top`). These
are shares of stacks, not savings. L1 can reach the 25%, L2 both.

**L1 versus L2.**

| | L1 | L2 |
|---|---|---|
| Change | `whnf`/`nf`/`conv` internals | the whole checker, `proof.rs` interfaces, `Ctx` |
| Differential testing | easy (old `whnf` as reference) | harder (different types) |
| Removes | per-beta body construction in reduction and conversion | also `infer`'s substitution |
| Keeps | `Expr`-based `infer`, tests, proof builders | only the input syntax |
| Cost | thunk cells with interior mutability; two representations | a new trusted core to audit |
| Eta | unchanged (none) | NbE makes eta natural; adding it changes the theory, so staying without it is a deliberate choice |

**Prototype before the kernel.** A closure-based `whnf` and `conv` can be
written as an untrusted module (for example `src/kernel_lazy.rs`, tests only),
checked against the kernel's `def_eq` on the reference tests and the lemma's
conversion queries, and timed. That measures L1's gain with no edit to
`src/kernel.rs`. Only a clear win justifies a design for the kernel itself.
