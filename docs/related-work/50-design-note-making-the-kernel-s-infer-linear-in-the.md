## 50. Design note: making the kernel's `infer` linear in the DAG

§48 and §49 left `infer` as the last tree walk on the proof path. This
note says what it would take, before any trusted code changes. Two
throwaway spikes (reverted) measured the options. Both use `\x. t_d`
from §48, with `denote`'s shared denotation.

**The spikes.**
- *Memo.* `infer` memoised on (address of the `Expr`, context length).
  That key is unsound in general, since the same node can be inferred
  under two contexts of the same length. It is exact for this term,
  which has one context.
- *Lazy substitution.* `subst_top(body, s)` returns `shift(body, 0, -1)`
  directly when `Var(0)` isn't free in `body`.

| `d` | neither | memo only | lazy `subst_top` only | both |
|---|---|---|---|---|
| 12 | not run | 3.5 to 4.7 ms | 3.0 ms | 0.13 ms |
| 16 | 0.7 s | 121 ms | 34 ms | 0.06 ms |
| 20 | 11.5 s | 2.25 s | 0.64 s | 0.08 ms |

Each cell is `infer` on the denotation, except the "neither" column,
which is §49's whole `prove_pure_expr`. Most of that is `infer`.

**Finding: the memo alone isn't enough.** With the memo on, `infer` made
only 67 calls at `d = 16` (32 hits), and still took 121 ms. The cost was
inside each call. `infer`'s `App` rule returns `subst_top(cod, a)`, and

```
fn subst_top(body: &Expr, s: &Expr) -> Expr {
    shift(&subst(body, 0, &shift(s, 0, 1)), 0, -1)
}
```

shifts the argument `s` in full before looking at `body`. For an
arithmetic operator `cod` is `Int`, which never mentions `Var(0)`, so
every application walks its whole argument, and `shift` has no cache
outside `with_shift_cache`. `subst`'s `Pi` and `Lam` cases do the same
once per binder they cross.

**Two changes, in order.**

*A. Lazy substitution in `subst_top`.* It has 22 callers in the kernel,
so fixing the shared function fixes all of them.
- A1, a guard: when `!is_var_free(body, 0)`, return
  `shift(body, 0, -1)`. That is equal to the old result, since `subst`
  is the identity when the variable is absent. It costs one extra walk
  of `body`, which is a type and usually small.
  - Pros: three lines, and obviously equal.
  - Cons: a dependent `body` still shifts `s` eagerly.
- A2, a fused `instantiate(body, s, depth)`: one pass over `body`.
  `Var(depth)` becomes `shift(s, 0, depth)`, higher indices drop by
  one, and `s` is shifted only where it is used. At depth 0 the shift is
  the identity.
  - Pros: never walks `s` unless it's substituted, including under
    binders.
  - Cons: a new traversal over every `Expr` variant, with the same
    binder bookkeeping as `shift` and `subst` (about 60 lines of trusted
    code).

A alone makes `infer` linear in the tree, and applies to every proof
with a large argument, not only shared ones. **Recommendation: A1,**
checked against the old `subst_top` on random `Expr`s (differential
test) and by `kernel_fuzz` and `kernel_soundness_fuzz`. A2 only if a
dependent-`body` case shows up in a profile.

*B. Memoise `infer` by (node, context).* Only this makes `infer` linear
in the DAG, which matters only for terms with heavy sharing, and the
corpus has none.
- Key: `(PtrKey, context id)`. A `PtrKey` holds its `Rc`, so an address
  can't be reused within the call, as with `ReductionCache`. `infer` gets
  an `Rc` form for children (`infer_rc`), and the top-level `&Expr` isn't
  memoised.
- Context ids: interned per top-level call, as `typing.rs` does (§45).
  Id 0 is the caller's context. Entering a binder whose type is the
  `Rc` `a` gives `intern(parent id, PtrKey(a))`. Equal ids then mean the
  same sequence of binder types, which is what `infer`'s result depends
  on. Keying on context length would be wrong: the same `body` under
  `Lam(A, _)` and `Lam(B, _)` has two types.
- Scope: one cache per public `infer`/`check` call, passed explicitly
  through private `infer_in`/`check_in` (and `infer_sigma`, `infer_pair`,
  `infer_sigrec`, `infer_sup`). This follows `def_eq`'s `ReductionCache`,
  not `with_shift_cache`'s thread-local, because hidden state is worse in
  trusted code than a wider signature.
- What's stored: only `Ok` results (an error ends the check), and only
  for nodes with `Rc::strong_count > 1`. A node reached twice has either
  that or a shared ancestor, which is memoised instead, so this keeps
  every walk linear. It also skips the hash-map cost on unshared terms,
  the common case, where `with_shift_cache` measured a regression when
  engaged unconditionally (see `with_shift_cache`'s doc).
- Optional: share one `ReductionCache` across the call's `def_eq`s.
  Reduction doesn't read the context, so this is sound.
- Why it's exact: `infer` is a pure function of the node's content and
  the context's content. Both are immutable behind the keys, which keep
  them alive.
- Tests:
  - a shared body under two different binder types (a length-keyed memo
    fails this);
  - on and off agree on every `kernel_fuzz` and `kernel_soundness_fuzz`
    term and every corpus proof, as `typing.rs`'s
    `the_memo_changes_no_answer` does;
  - a call-count bound on a shared term.
- Cost: about 60 lines of trusted code, and a signature change across
  `infer`'s helpers.

**Alternatives considered.**
- *Thread-local scope*, like `with_shift_cache`.
  - Pros: no signature changes.
  - Cons: hidden state in the kernel, and its nesting rules become part
    of what has to be trusted.
- *Hash-consing kernel `Expr`s.*
  - Pros: sharing everywhere, and `==` in O(1).
  - Cons: every constructor changes. By far the largest option.
- *Sharing in the proof term, not the kernel.* `denote` emits a
  beta-redex, `(\y: Int. y + y) a`, for a shared `a`. With A, the kernel
  checks `a` once and the body once, with no memo.
  - Pros: no trusted change beyond A.
  - Cons: the theorem's statement changes from `d` to a
    beta-equivalent `d'`. `denote` must choose where to bind. And `nf`
    would need A2, since beta-reduction substitutes `a` under the
    redex's own binder.

**Order.** A1 first: small, exact, and useful beyond sharing. Then B only
if sharing-heavy terms matter, and then together with sharing in the IR
and `eval` (§48's steps 4 and 5). Until all of those land, §47's gate is
what bounds a shared term's cost.

A1 landed in §51.

