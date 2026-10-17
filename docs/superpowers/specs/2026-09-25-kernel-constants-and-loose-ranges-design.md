---
status: done
---

# Constants, free parameters, and cached loose ranges: design

Status: design and spike done (RELATED_WORK.md §64); stage 1 built (§65),
stage 2 built (§67), stage 3 built as 3a (§69) and 3b (§70), stage 4 built
(§72). It replaces
§50-§63's one-at-a-time memos and workarounds with the representation Lean
and Isabelle build them from. Every stage that touches the kernel changes
trusted code, so each needs an explicit go-ahead before it's built.

## Goal

Make proof terms keep their sharing through `shift` and `instantiate`, so a
proof built as a DAG is checked, stored and freed as one.

Today two things combine to stop this:
1. Postulates and the builder's scope parameters are de Bruijn variables at
   the end of the context. So every term the builder makes has free
   variables, and whenever the context grows under a term, the term has to
   be shifted.
2. `shift` and `instantiate` rebuild every node they visit, so a shift
   returns a tree even when its input was a DAG.

§62's prepass, §63's `infer` memo, `Anchored`, `Params` and the closure
priming (`prime_closure_postulates`) all work around one or both of these.
`fib(16)`'s instance proof still has 265k DAG nodes and takes about 1.9 s
to prove and re-check.

## The representation

Three kinds of variable, each with its own numbering:

| | `Const(l)` | `Free(l)` | `Var(k)` |
|---|---|---|---|
| What | a postulate (axiom) | a builder scope's parameter or local, not yet closed | a variable bound inside the term |
| Numbered by | de Bruijn level in the global environment | level, from a counter that never reuses one | de Bruijn index |
| Typed by | `globals[l]`, closed | the builder's params stack; the kernel never types it | the kernel's binder context |
| Kernel `infer` | `globals[l]` | **rejected** | as today |
| Shifted by a push? | no | no | only by binders it's under |

This is Isabelle Pure's `Const` / `Free` / `Bound`, and Lean 4's `const` /
`fvar` / `bvar`, with integer levels in place of names. The kernel's own
binders stay de Bruijn indices: the kernel doesn't open binders into
`Free`s the way Lean's does (that costs an `instantiate` per binder
entered, and nothing here needs it).

## Decisions (and the options they beat)

- **Two level spaces, `Const` for globals and `Free` for builder
  parameters.** The spike found that no kernel `check` or `infer` ever runs
  while a builder scope is open, and that every push inside a scope is a
  local (params, the `v`/`e`/motive/ih binders, per-path premises), never a
  lazy global. So the kernel only ever needs to type globals. The options
  this beat:
  - *Postulates as levels, params as `Var`s* (this spec's first draft). It
    works, and costs the same (§64), but params still shift, so `Params`
    and `Anchored` stay, and a term that escapes its scope is silently
    reinterpreted wherever it's reused.
  - *One level sequence for both, reused after a scope closes.* It needs no
    new variant, and is safe today only because of the two facts above,
    which nothing enforces. A parameter that leaks into a checked term is
    then just another context entry, so it silently acts as an **unproven
    axiom** (a leaked `e : Ev(...)` proves anything about `Ev`). A term
    that escapes its scope refers to whatever reuses its level next. A
    global pushed inside a scope is truncated with it, which is why the
    priming exists.
  - *One sequence, never reused, with dead entries as tombstones the kernel
    rejects.* Mistakes fail loudly, but `close` then abstracts an explicit
    list of levels, dead entries pile up in the environment, and a global
    pushed mid-scope sits between the params, which defeats the max-level
    skip below.
  - *Postulates by name, as in Lean.* A symbol table only to get what a
    level already gives, since postulates are only ever appended.
- **`Free` levels are never reused.** A counter hands them out; the params
  stack holds the live ones, in increasing order. A term that escapes its
  scope keeps a `Free` no enclosing scope binds, so `close` leaves it and
  the final `check` rejects it. Reuse would let a later scope capture it
  silently. Cost: `close` finds a level's binder by binary search in the
  stack rather than by subtraction, and a `u32` counter (debug-asserted not
  to wrap) outlives any build.
- **The kernel's `Ctx` becomes `{ globals, locals }`.** `Const(l)` is valid
  only for `l < globals.len()`: it must never resolve to a binder the
  kernel pushed itself. (The spike's `ctx.get(l)` breaks this, which is
  fine in throwaway code.) With a single context and a count of globals, a
  `Const` that points at a binder breaks beta reduction:
  `(λx:A. Const(L)) a` would reduce to a `Const(L)` that no longer refers
  to anything. The split makes that impossible. (Built instead as
  `Globals` beside `Ctx`, the same separation; see stage 2 and
  RELATED_WORK §67.)
- **Each heap node caches two ranges.** `loose`: one more than its largest
  loose `Var`, 0 if none. `free`: one more than its largest `Free` level,
  0 if none. `shift` and `instantiate` return a child unchanged, by
  pointer, when `loose` shows they'd be the identity on it. `close`
  returns a child unchanged when `free` is at most the scope's first
  level. As in Lean's `Expr.Data` (`looseBVarRange`, `hasFVar`) and
  Isabelle's `loose_bnos`. The options this beat:
  - Rocq's approach (`Constr.map` returns the same pointer when no child
    changed): it keeps sharing but still walks every node.
  - A memo on `shift`: keyed by (node, cutoff, amount). It allocates a
    table per call, and it doesn't fix `instantiate`.
  - Hash-consing: `==` in O(1), but it needs a global table, and a shift
    still copies. §64 compares the two.
- **No memo on shared nodes inside a traversal, for now.** Lean's
  `replace_rec_fn` (`src/kernel/replace_fn.cpp`), which every
  `instantiate`, `lift_loose_bvars` and `abstract` goes through, keeps a
  per-call map from (node, binder offset) to its result for nodes with a
  refcount above 1, so a shared *open* subterm is rebuilt once and stays
  shared. The spike measured it (§64): it was idle, with 0 hits in 375
  and 5,605 lookups for `gcd`'s universal proof and `fib(16)`'s instance
  proof, and 1% to 2.5% with parameters as levels. A shared node is
  almost never reached twice in one traversal here. It's the known remedy
  if a workload ever rebuilds shared open subterms, and the same trick as
  §63's `infer_rc`.
- **The cache lives in a kernel-local `Rc`**, not in `Expr`'s variants. The
  kernel's children are `Rc<Expr>` already. A kernel `Rc<T>` wrapping
  `std::rc::Rc<Node<T>>`, with `Node { loose: u32, free: u32, val: T }`,
  keeps every pattern (`Expr::Pi(a, b)`), constructor (`Rc::new`) and
  helper (`Rc::ptr_eq`, `strong_count`, `as_ptr`) compiling unchanged. The
  spike touched 4 match arms outside the traversals. `loose` makes the
  node 56 bytes (a 48-byte `Expr` plus a `u32`, padded to 8), and `free`
  fills that padding, so both cost 8 bytes: 72 with the `Rc` header,
  against 64 today. The options this beat:
  - A field in every variant, or `struct Expr { data, kind }`: every
    pattern in the crate changes.
  - A side table keyed by pointer: a hash lookup at each node, which is
    what the cache exists to avoid.
- **No cached hash for now.** The spike measured it (§64). Nothing
  consumes it yet: `def_eq`'s `==` is already linear (§61), and there is
  no hash-consing table. It costs another 8 bytes on every node. Add it
  when a consumer appears.
- **No shared checker state (the "one struct for all caches" option).**
  The spike threaded one `ReductionCache` through a whole `check`, used by
  every `def_eq` and `whnf` inside it. On `fib(8..16)` it made no
  difference once constants and loose ranges were on. With them off it
  was up to 45% slower. The likely cause, not profiled, is that the cache
  keeps every intermediate term alive until the check ends.
  §64 has the numbers. Each `def_eq` keeps its own cache.

## Semantics

**`Expr::Const(u32)`.** Constant `l` has type `globals[l]`.
- `infer`: `Const(l) : globals[l]` when `l < globals.len()` and
  `globals[l]` has `loose` and `free` both 0. Otherwise it's an error. The
  type is returned as is, since it has no variables to shift.
- `whnf`, `nf`: `Const` is neutral, like a `Var`, and has no definition to
  unfold.
- `same_shape`, `==`, `def_eq`: `Const(i)` matches only `Const(i)`.
- `shift`, `instantiate`, `is_var_free`: `Const` has no variables, so these
  are the identity on it.
- `Debug`: `@l`, beside `Var`'s `#k`.

**`Expr::Free(u32)`.**
- `infer` and `check`: an error ("free parameter escaped its scope").
  This is the rule that makes a leaked parameter a failed check rather than
  an axiom, the analogue of locally nameless's "only locally closed terms
  are typed".
- `whnf`, `nf`, `def_eq`: neutral, and `Free(i)` matches only `Free(i)`.
  So structural helpers still work on the builder's open terms.
- `shift`, `instantiate`, `is_var_free`: the identity.
- `Debug`: `$l`.

**The environment.** `Ctx` becomes a struct with two public fields:
`globals: im::Vector<Expr>` for constants, and `locals: im::Vector<Expr>`
for the kernel's binders, which is exactly today's `Ctx`. The kernel pushes
binders onto `locals`, and `ctx_lookup` reads `locals`. The public
`infer(ctx, e)` and `check(ctx, e, ty)` keep their signatures, so the 64
`check` sites in `proof.rs` and the proof records' `ctx` fields don't
change. (Built instead as `Globals` beside `Ctx`, with the same
separation; see stage 2 and RELATED_WORK §67.)

The environment gets the same trust as today's context: nothing checks
that each entry is a type, and a postulate is an axiom. What the kernel
does enforce is that a global's type is closed (no loose `Var`, no `Free`).

**Ordering: a global's type mentions only earlier globals** (`Const(j)` in
`globals[l]` needs `j < l`). Today this holds by construction, since a
context entry's `Var`s can only point further out. With levels, a forward
or circular reference becomes expressible. It can't make the kernel loop
(a `Const` never unfolds, and `infer` returns `globals[l]` without
inferring it), so, like "each entry is a type", it's enforced where
entries are made rather than in the kernel: `Postulates::push` walks the
type once and panics on a `Const` at or above the new level. Nothing in
the builder needs forward references; a sorry-style placeholder is the only
use found for them.

**`close`.** `close_pi(scope, body)` and `close_lam(scope, body)` take the
scope's first `Free` level and the params stack. For each live parameter at
or above it, outermost first, they wrap a binder whose domain is that
parameter's type, and turn each `Free(l)` in the body (and in later
parameters' types) into the `Var` for its binder. A child whose `free` is
at most the scope's first level is kept by pointer. A `Free` below the
scope belongs to an enclosing scope and is left alone. A `Free` at or above
the first level that isn't live has escaped from a closed scope; it's left
alone too, and the final `check` rejects it.

**Loose and free ranges.** `loose(Var(k)) = k + 1`, `free(Free(l)) = l + 1`,
and every other leaf has 0 for both. A node's `free` is the maximum over its
children. Its `loose` is too, except that a child one binder deeper
contributes its own range minus one. The children one binder deeper are the
ones `shift` gives `cutoff + 1` today: `Pi`, `Lam`, `W` and `Sigma`'s
second field, `WRec`'s `children_ty`, and `Pair`'s `fam`.
- `Rc::new` computes a node's ranges from its children's cached ones, so
  it's O(1). A top-level `Expr` that isn't behind an `Rc` computes them the
  same way.
- `shift(x, c, n)` is the identity when `loose(x) <= c`.
  `instantiate(x, s, d)` is the identity when `loose(x) <= d`: no variable
  of `x` is at or above `d`, so none is replaced or renumbered.
  `is_var_free(x, i)` is false when `loose(x) <= i`.
- A cached range is right because nodes are immutable. The kernel `Rc`
  exposes no `get_mut` or `make_mut`. When the stack runs low,
  `Drop for Expr` swaps a shared `Sort(0)` into the child slots of a node
  that's being freed. That node's cached ranges go stale, but nothing
  reads them again.

## Stages

Each stage is one commit behind the full validation. Each has its own
tests and its own go-ahead.

**Stage 1: loose ranges** (trusted; no change to any answer).
- The kernel `Rc` and `Node` (with `loose` only), `loose_of`, and the fast
  paths in `shift`, `instantiate` and `is_var_free`. `shift` and
  `instantiate` build nodes from `Rc`s they keep, rather than through
  `pi()` and the other `Expr`-taking builders, so an unchanged child keeps
  its pointer.
- `shift_sigma_family` stays. Rechecked in stage 1: its reason (at
  `infer_sigma`) is only that smaller hot frames cost nothing, and that still
  holds.
- `proof.rs`'s two test uses of `Rc` on kernel nodes import `kernel::Rc`.
- Payoff alone: about 20% on `fib(16)`, since today almost nothing is
  closed. Measured: 11 to 14% (RELATED_WORK §65). The 20% came from a
  loaded machine; the spike reruns idle at 12%.

**Stage 2: `Const` and `Free` in the kernel** (trusted). Built (§67).
The environment is a separate `Globals` vector beside `Ctx`, with
`infer_in`/`check_in`, rather than `Ctx { globals, locals }`, since
`proof.rs` uses `Ctx` as an `im::Vector` (§67).
- `Expr::Const` and `Expr::Free` with the rules above, `Node.free`, and
  `Globals` beside `Ctx`.
- `kernel_soundness_fuzz` and `kernel_fuzz` generate `Const`s over a small
  environment, and `Free`s, which must never type-check. Their exhaustive
  matches gain the arms.
- Nothing in `proof.rs` produces either yet, so every answer is unchanged.

**Stage 3: the builder uses them** (untrusted: `proof.rs`, and `Postulates`
and `close_pi`/`close_lam` in the kernel module). Built in two halves:
3a, postulates as `Const`s (§69), and 3b, parameters as `Free`s (§70).
Where the build departs from the bullets below:
- `push`'s ordering check is its `infer` to a `Sort` against the earlier
  globals, not a separate walk (§69).
- Any `push` inside an open scope panics, not only one whose type
  mentions a parameter, so the "extra global" case below can't happen.
- `close` memoises shared nodes as well as skipping by `free` (§70).
- `close_pi`/`close_lam` are deleted; `close` builds the binders.
- `Postulates` holds `globals` (the kernel `Globals`), the params stack of
  live `(level, type)`s, and the next `Free` level. Its check sites (the
  64 in `proof.rs`) move to `check_in`/`infer_in`, passing `globals`
  alongside the local `ctx` they already pass.
  - `push(ty)` appends a global and returns its level, after checking
    that `ty` is closed and mentions only earlier globals. `get(level)` is
    `Const(level)`.
  - `bind(ty)` pushes a parameter and returns its `Free`.
  - A scope records the stack's length and the next level on entry; its
    `close` abstracts from that level, then truncates the stack.
- `params_and_close`, `params_and_close_typed`, and the `ev_rec_ty` scope
  in `build_universal` bind their parameters, and so do the binders their
  `build` closures add (`v`, `e`, motives, ih, `push_path`'s premises).
- `Params` holds the parameters' `Free`s directly: they no longer go stale,
  so the snapshot bug it exists to avoid is gone.
- A local pushed with `push` by mistake fails loudly when its type
  mentions a parameter, as `e`'s, the ih's and every premise's do: `push`
  panics. One with a closed type (`v : Int`) becomes an extra global
  instead, and `close` doesn't wrap it (see Risks). A parameter that leaks
  into a checked term fails the check. All corpus proofs are re-checked by
  the existing tests.
- Payoff, with stage 1 (spike): `fib(16)` from about 1.9 s to about 19 ms,
  and its DAG from 265k nodes to 10.5k. Params as levels on top cost
  nothing measurable (§64): closing rebuilt 600 to 840 nodes, against
  3.5k to 35k for the kernel's `instantiate`.
- Constraints from stage 2's final review (RELATED_WORK §67):
  - The next `Free` level only grows: `close` must not restore it. If
    sibling scopes reused levels, a `Free` leaked from one would be
    abstracted into a bound `Var` by the next one's `close` instead of
    failing the check.
  - `push`'s ordering check (`Const(j)` in `globals[l]` needs `j < l`) is
    a full walk: the kernel checks only that a global's type is closed,
    and there's no room in the 56-byte `Node` for a cached `Const` range.
  - A check site left on `check` fails loudly ("unknown constant"),
    since `check` passes no globals.
  - `check_in` now checks that `expected` is a type (§68); `push` checks
    each global's type the same way, once.
  - An `InferCache` shared across calls would need the globals in its
    key. Entries stay valid while `Globals` only grows.
  - `close` can skip by pointer any subterm whose `free` is at most the
    scope's first level, as stage 1 does with `loose`.

**Stage 4: remove what no longer pays** (untrusted). Measure each one
first, then delete it:
- §62's prepass (`push_ev_facts`): a postulate pushed mid-build shifts
  nothing, so memo hits share without it.
- `Anchored`: a term built from `Const`s and `Free`s has no loose `Var`s,
  so `at` is the identity. It should go entirely.
- `Params`: becomes a plain `Vec<Expr>`, or goes.
- `prime_closure_postulates` and the `clo_ty` priming loop in
  `build_universal`: they exist so a lazy global isn't pushed inside a
  scope and truncated with it. Globals are no longer truncated, but
  `push` panics inside a scope (§70), so removing the priming means
  relaxing that panic: let a lazy global be pushed mid-scope, since a
  `Const` shifts nothing. That also removes the JIT's panic path on a
  missed prime.
- The fixed cost of `push`'s check (§69): ~4 µs a proof, half of a
  µs-scale proof, most of it rebuilding and re-checking the same
  `ArithPostulates` prelude every proof. Not decided: build the prelude
  once and share it, or skip the check for built-in entries.

**Built** (RELATED_WORK.md §72): all four items above, plus relaxing
`push`'s scope-open panic so the priming could go. `push_ev_facts` was not
kept — it was measured, then deleted like everything else here.
`Anchored` and `Params` are both gone entirely, not narrowed to a plain
`Vec<Expr>`. One exception: the literal pre-pass loop in
`clo_eq_ref_if_tree` (and its twins in `call_eq_ref` and `build_universal`)
was kept, since `denote`'s `lit_ref` panics on a literal that wasn't
pre-postulated — unrelated to the scope-panic mechanism this stage
removes. The prelude cost above was not addressed by this stage; it's
handled separately by `ArithPostulates::new`'s thread-local prelude
(commit 7e6d61c).

## Testing

- **Stage 1.**
  - `loose_matches_a_walk`: on random terms, every node's cached range
    equals the one a direct walk computes. A wrong binder adjustment
    (`loose(b)` in place of `loose(b) - 1` under `Pi`) must fail it.
  - `shift_and_instantiate_match_a_reference`: on random terms, the new
    `shift` and `instantiate` agree with today's (kept in the test module
    as the reference) under `==`.
  - `shift_keeps_closed_children_by_pointer`: `shift` of
    `App(closed, Var(0))` returns the same `closed` `Rc`.
  - `dropping_a_deep_term_does_not_overflow_the_stack` drops a
    100,000-deep `refl` chain on a 1 MB thread. It aborts if the wrapper's
    `strong_count` is off by one. `check_survives_a_term_far_deeper_than_the_native_stack_allows`
    doesn't: its 1,000-deep terms drop fine even unprotected.
  - `infer_memo_changes_no_answer` currently unshares with `shift` by 1 and
    back, which will now keep closed subterms shared. It needs a real deep
    copy instead, or the test loses its teeth.
- **Stage 2.**
  - `Const` out of range is rejected, and so is a `Const` whose level is
    a kernel binder's position (the `Globals`/`Ctx` split).
  - A global whose type has a loose `Var` or a `Free` is rejected when
    used.
  - `Free` is rejected by `infer` and `check`, including under a binder
    and inside a type.
  - `(λx:A. Const(0)) a` reduces to `Const(0)`, so `Const` isn't
    substituted.
  - `Const(0)` and `Const(1)` aren't `def_eq`; nor are `Free(0)` and
    `Free(1)`, nor `Const(0)` and `Free(0)`.
  - `free_matches_a_walk`, as for `loose`.
  - The fuzzers' soundness properties hold with both in the grammar.
- **Stage 3.**
  - Every proof test re-checks as before.
  - `close_pi` over `Free`s equals a hand-built dependent `Pi` chain
    (rewriting `close_pi_matches_hand_built_dependent_pi_chain`).
  - A `Free` that escapes its scope is left by a later scope's `close` and
    rejected by `check`; with level reuse this test would pass wrongly, so
    it's the teeth of "never reused".
  - `push` panics on a type with a `Free`, and on a forward `Const`.
  - `infer_is_linear_in_the_dag_of_a_shared_term` builds its postulates
    as `Const`s.
  - `a_fibonacci_instance_proof_shares_its_repeated_witnesses` tightens to
    linear growth. The spike's DAGs were 5,445, 7,973 and 10,501 nodes at
    `fib(8, 12, 16)`, so require `dag(fib16) < 2.5 × dag(fib8)`.
  - A timing guard on `fib(16)` in the style of §63's tests.
- **Every stage:** best-of-3 interleaved criterion runs against a
  re-baseline taken just before the stage, on an idle machine or with
  the load reported. Then `scratchpad/validate.sh` (build, lib tests,
  clippy, the release fuzzers, `ir_fuzz`, `cargo run --release`), and a
  mutation of each fix to show its test catches it.

## Risks

- **Memory.** Each node grows from 64 to 72 bytes on the heap (Rc header
  plus a 48-byte `Expr`, plus the two ranges), 12.5%. Stage 3 more than
  repays it on shared proofs. On unshared ones it's the whole effect. §64
  has the measured overhead.
- **A wrong range is unsound.** An underestimated `loose` makes `shift`
  skip a variable it should renumber. An underestimated `free` makes
  `close` leave a parameter free, which only fails the check. That's why
  stage 1 has the walk-agreement test, the reference differential and the
  fuzzers.
- **A local pushed as a global.** If its type is closed, nothing fails:
  it's an extra axiom, and the theorem lacks that binder. Today's code has
  the same hole, since `push` is the only way to add anything. Converting
  each in-scope `push` in stage 3 is mechanical (the spike's stats list all
  of them, by line), and a proof whose theorem lost a binder no longer
  matches its caller's expected type, which is how today's tests would
  notice.
- **A builder call to the kernel inside a scope.** The spike saw none, but
  if one is added, a term with a `Free` is rejected rather than checked
  against a context holding the parameter. That's a loud failure; the fix
  is to check after `close`, as every current site does.
- **Deep drops through the new `Rc`.** `Drop for Expr` frees a deep term
  without overflowing the stack: when the stack runs low it swaps a shared
  `Sort(0)` leaf into each child slot it would free (`strong_count == 1`)
  and drops the child on a fresh stack segment. The wrapper's
  `strong_count` must reach the inner `std::rc::Rc`, or a deep proof
  crashes when it's freed. `check_survives_a_term_far_deeper_than_the_native_stack_allows`
  isn't the guard: it passed with `strong_count` off by one, since its
  1,000-deep terms drop fine by plain recursion. The guard is
  `dropping_a_deep_term_does_not_overflow_the_stack`, which drops a
  100,000-deep `refl` chain on a 1 MB thread and aborts under that
  mutation.
- **The `Globals`/`Ctx` bound is trusted code.** A `Const` resolved
  against anything but `globals` (one combined vector, say) can reach a
  kernel binder, and beta reduction then leaves it dangling. Stage 2's
  test with a `Const` at a binder's position is the guard, with the same
  mutation check as every fix.
- **Unfuzzed rules.** `kernel_fuzz` and `kernel_soundness_fuzz` match
  exhaustively on `Expr`, so they stop compiling until they gain the new
  arms, which is good. But arms alone leave `Const` and `Free` unfuzzed.
  Their generators must produce both, and any term with a `Free` that
  type-checks is a failure.
- **Noise hides regressions.** On this machine one config's criterion
  times varied 2× to 3× between rounds even when the CPU looked mostly
  idle, and a single round once showed a 7% to 85% slowdown that didn't
  reproduce (§64). So each stage is judged by best-of-3 interleaved runs
  against a re-baseline taken just before it, and by structural guards
  that noise can't move: DAG sizes, and work counters where a stage
  claims to remove work.

## Future directions

What levels give up relative to today's all-`Var` context, and how each
could come back if wanted:
1. **Abstracting a global into a binder** (a generic lemma over
   per-function postulates, discharging an arithmetic axiom, a closed
   theorem statement). Parameters get this from `close`. For globals it
   would be a deliberate `Const`-to-`Var` pass, written when a use appears.
2. **Forward and circular references.** Ruled out by the ordering rule;
   only a sorry-style placeholder would want them.
3. **Moving a term between environments** (f's proof calling g's, a proof
   cache keyed by the JIT's `Hash`, parallel builds). A `Const` level only
   means something in its own environment, so this needs a relabelling
   pass, content-addressed ids for globals, or one shared persistent
   environment. It matters once modular proofs or a proof cache exist.

Also deferred:
- Opening the kernel's own binders into `Free`s, as Lean's kernel does.
- A cached hash with hash-consing (§64). Rocq hash-conses each constant's
  body once, when it's added to the environment (`safe_typing.ml`),
  because the environment keeps it. Nothing here keeps a proof term: the
  JIT stores only a `ProofStrength` per `Hash`. It becomes worth doing
  with a proof cache (3 above), where the same hashes can also serve as
  content-addressed ids.
- The traversal memo above, if a workload shows shared open subterms being
  rebuilt.
- Other allocation strategies (§64 surveys them). `Rc` stays for stages
  1-4, since everything here was measured on it, and the kernel `Rc`
  wrapper keeps these local:
  - An `Rc` with no weak count: an 8-byte header, as Lean's objects have,
    brings nodes back to 64 bytes, at the cost of `unsafe` code in the
    trusted kernel.
  - A faster global allocator (mimalloc): adopted. RELATED_WORK §66:
    the proof benches 38 to 52% faster, the interpreter 13 to 28%, the
    cold JIT 19 to 35%, warm JIT unchanged.
  - nanoda_lib's per-check arenas of hash-consed 32-bit ids: a rewrite of
    every constructor and pattern, but it gives hash-consing, stable ids
    for a proof cache, and free-all together. Worth revisiting alongside
    3 above.
