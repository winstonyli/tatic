---
status: done
---

# Proof plans: the rewriter decides, a compiler proves

**Goal:** the rewriter builds no kernel terms. It returns the rewritten term and a *plan* (how the rewrite is justified); a
compiler turns the plan into a kernel proof only when a caller wants one. Counting (`RULEMINER_FAST`) never compiles.

**Why:** the cmp3d profile (docs/tier-cycle.md, "Where the time goes after it") has `hc::intern` at 58% of the mine process,
almost all of it proof terms the counting-only rewriter builds and drops: `ev` endpoints, `cong_n`/`trans_proof`, `witnessed`,
`ops_for`, and `add_tree_law`'s whole n-bit proof (built with placeholder lemmas and, under `SCORE_ONLY`, not even cached).
The five decisions that read kernel terms now use plain Booleans (`Bools`, the commit before this plan), so the rewriter's
choices no longer depend on any `Expr`.

**Spec:** docs/tier-cycle.md, "Decisions that read kernel terms (2026-10-12)" and the proof-plan paragraph before it.

## Global constraints

- Sweep rows, rule files, unit files and preference files identical to the commit before, on salts 1 and 2 (`RULEMINER_FAST=1`).
- No compat shims: `rewrite`'s `ops`/`goods` parameters go; callers are fixed once.
- Every proof the compiler builds is kernel-checked by the existing tests (71) and by serving in the sweep.

## The plan type (rewrite.rs)

```rust
/// How a rewrite `lhs = rhs` is justified; `compile` turns it into a kernel proof.
pub enum Plan {
    /// t = t
    Refl(Term),
    /// o(a, b) = o(a', b') from a = a' and b = b' (an `lt` gives one bit)
    Cong(usize, Rc<Plan>, Rc<Plan>),
    /// a = c from a = b and b = c
    Trans(Rc<Plan>, Rc<Plan>),
    /// b = a from a = b
    Sym(Rc<Plan>),
    /// a closed law over pattern variables V(0..args.len()), at the terms `args`
    Law(Law, Vec<Term>),
}
pub struct Law { pub kind: LawKind, pub lhs: Term, pub rhs: Term }
/// Which prover proves the law: also its lemma identity
pub enum LawKind { Rule(&'static str), Assoc, Comm, Bitwise, Chain, Tree }
```

Every lemma instance today is `apps(law, values of args ++ witnesses of args)`, so one `Law` node covers all of them:

| Site | Law | args |
|---|---|---|
| `rule_step` | `Rule(name)`, `prove_rule(n, k, lhs, rhs)` as a shared lemma | `sub`, unbound filled with `V(0)` (today's `goods[0]`) |
| `shr_mask_eq` side | `Rule("shrmask")`, `shr1 x -> shr1 (x & shl1 -1)` | `[arg]` |
| add branch | `Assoc` (`add_assoc_proof`), `Comm` (`add_comm_proof`) | `[p,q,r]`, `[a,b]` |
| collapse, `eq_truth`, `eq_pos`, bitwise swap | `Bitwise`, `bitwise_law_k(n, k, lhs, rhs)` | atoms padded with `V(0)`, or `V(0..k)` |
| `chain_step` | `Chain`, `carry_chain_law(n, lhs, rhs)` | two atoms padded with `V(0)` |
| `tree_step`, `machine_fallback` | `Tree`, `add_tree_law(n, k, lhs, rhs)` | `V(0..k)` |

`bitwise_law(n, ..)` is `bitwise_law_k(n, 2, ..)`, so the swap is `Bitwise` too. `shrmask` is `prove_rule(n, 1, ..)` already.

## Compiler

`fn compile(n: usize, k: usize, plan: &Plan) -> (Term, Term, Expr)`: lhs, rhs and the proof, bottom up, with one context
per call holding `ops_for(n)`, the goods `(var(2k-1-i), var(k-1-i))` and their values. Endpoint types: `bv_ty(1)` when the lhs
root is `lt`, else `bv_ty(n)`; `Cong` uses `cong_n(bv_ty(n), that type, ops[o], ..)`. Law args go through `witnessed` (value and
witness), endpoints through `eval`, as today. `Rule`, `Assoc`, `Comm` go through `shared_lemma` with today's keys; `Tree`
through `add_tree_law` (its cache); `Chain`, `Bitwise` are built per instance as today.

## API

- `rewrite(t, n, k) -> (Term, Rc<Plan>)`; `rule_step`, `chain_step`, `tree_step` return `Option<(Term, Rc<Plan>)>`; `prove_eq`,
  `shr_mask_eq`, `machine_fallback` return `Option<Rc<Plan>>`.
- `rewrite_plan(n, k, t1, t2) -> Option<Rc<Plan>>` decides; `rewrite_law(n, k, t1, t2) -> Option<(Expr, Expr)>` is
  `rewrite_plan` + `compile` + the binders (as today). Callers that only ask `is_some()` (score_laws, the base pass,
  `law_cost`, `check_rules` under `CHECK_FAST`, ...) call `rewrite_plan`.
- `RewriteMemo` stores `(Term, Rc<Plan>)`, keyed as today (`goods_len` becomes `k`). Plans do not depend on the mode, so
  entries made while counting and while proving are interchangeable.

## add_tree_law split (machine.rs)

`tree_encoding(n, k, t1, t2) -> Option<Rc<TreeEnc>>` (everything up to the found `(enc, inv)`) and the proof part;
`add_tree_law` is the two composed with the proof cache `TREE_LAWS`. `tree_step` and `machine_fallback` (proving) ask only
`tree_encoding`. Its cache (per thread, by `(n, k, t1, t2)`, all modes: a pure function of them) holds only pairs past the
cheap screens (`plausibly_equals`, parse, carry cap), so `tree_step`'s many failing candidates cost no memory. Counting mode
cached nothing before, so this cache is new memory there; `PROF` then times cache misses only.

## What `SCORE_ONLY` still means

Only `machine_fallback`'s screen: while counting, a fallback is taken when 16 tuples agree, not when an encoding exists.
A plan made under it may not compile. `shared_lemma`'s placeholder branch and `add_tree_law`'s don't-cache guard go: nothing
builds lemmas while counting.

## Inner proofs get a fresh rewriting context

`prove_rule` and `shr_not_law` prove a rule by rewriting (`rewrite_law` with the rule blocked in `PROVING`). Today that
runs in the middle of the outer rewrite (proving mode only) and leaks into it: the outer `REWRITE_PATH` can cut the inner
rewriting, the inner results (made with a rule blocked) go into the shared `REWRITE_MEMO`, and the inner rule steps and
fallbacks land in the outer law's `RULE_TRACE` and `MACHINE_FALLBACKS`. One helper, `proving(blocked, f)`, saves and
restores `PROVING`, `REWRITE_PATH`, `REWRITE_MEMO`, `RULE_TRACE`, `RULE_BUDGET` (10 000 inside, as `prove_rule` sets now) and
`MACHINE_FALLBACKS` around both. With plans the inner proofs run at compile time, after the outer rewrite, so only proving
mode changes, and toward what counting mode already does.

## Tasks (inline; one tightly coupled change)

1. `tree_encoding` split and its cache; `add_tree_law` composed from it. Tests pass.
2. `Plan`, `Law`, `compile`; the rewrite family returns plans; `rewrite_plan`/`rewrite_law`; callers; `proving` helper;
   `shared_lemma`/`add_tree_law` counting branches deleted; doc comments. New test `plans_compile_to_checked_proofs`: for a
   handful of laws (assoc+comm, collapse, chain, tree, shr mask, `lt` root), `rewrite_plan` is `Some` under `SCORE_ONLY` and
   not, and `rewrite_law`'s proof checks. Tests pass.
3. Pair sweep (both salts) against the item-1 commit: rows and files identical; wall time. Profile cmp3d again.
4. Docs: tier-cycle.md section with the result; learned-vs-fixed unchanged (no learned part moves); runs README row.

Parked: typed lemma keys (`CLOSED` keyed by `LawKind` + terms, the `guarded` tree key, `Machine::key`): after this plan
the counting path formats no keys, so they are a cleanliness change, not a speed one. `ops_for` per width cached: proving
only after this plan; measure with the new profile first.
