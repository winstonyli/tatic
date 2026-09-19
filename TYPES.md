# The closures fragment's type system

`compile.rs` and `proof.rs` together implement a small, informal type
system for the "first-order arithmetic with self-recursion and closures"
fragment described in `compile.rs`'s own module docs. It has never been
written down as one thing — it's assembled from several independently-
computed pieces, spread across both files, that happen to agree with each
other by construction rather than by being checked against a single
specification. This document states it as one system: its grammar, its
types, its typing judgment, where each rule is actually implemented, and
— the main finding of writing it down — a real gap between what the
system's types claim and what the kernel actually checks.

It formalizes what's *already implemented*. See the very last section for
what a more principled version could look like, and why that's a
materially bigger, separate piece of work.

## 1. The fragment's grammar

Every rule below is over `term.rs`'s `Term` enum, restricted to the
"compilable fragment" `compile.rs`'s own module docs define: closed
expressions built from `Var`/`Lit`/`Prim`/`If`, fully-saturated self-calls
(optionally `Rec`-wrapped), applications of a variable or a literal
lambda ("combinator"), an under- or over-applied literal lambda, and a
literal lambda used as a bare value. A term outside this fragment simply
has no typing derivation below — `None`, propagated with `?` throughout
both files, not a stuck or ill-typed judgment.

## 2. Types

Two types, in the sense that every subterm in scope denotes as one or the
other:

```
τ ::= Int | Clo
```

`Int` is the kernel's postulated `Int : Sort(0)` (`ArithPostulates::new`).
`Clo` is the kernel's postulated `Clo : Sort(0)` (`ClosurePostulates::new`)
— **one single type**, not a family indexed by arity. This is the crux of
section 6 below: every closure value in this fragment, whatever its real
arity, has exactly the same kernel-level type. Arity is tracked entirely
*outside* the kernel type, as a side channel threaded through Rust values
(`Option<usize>`, `None` meaning `Int` and `Some(k)` meaning "a closure
always called with exactly `k` arguments" — this document writes that as
`Clo_k` where the distinction matters, but stress: `Clo_k` is not a real
kernel type; it's `Clo` plus an out-of-band arity `k` that nothing at the
kernel level ever inspects).

## 3. Contexts

A context `Γ` is a finite map from a de Bruijn `Var` index (`0..arity`,
one combinator's own declared parameters) to `Option<usize>` — `Γ(i) =
Some(k)` reads as `Γ ⊢ i : Clo_k`, `Γ(i) = None` as `Γ ⊢ i : Int`. In code
this is `param_types: Vec<Option<usize>>` (or `ctx.closure_arities` on
`compile.rs`'s side, computed by the identical algorithm — see below).

`Γ` is computed once per combinator, *before* any typing derivation over
its body runs, by a separate inference pass — not part of the typing
judgment in section 4, but its precondition.

### 3.1 Inferring `Γ`: `infer_closure_arities` / `scan_for_closure_calls`

(`compile.rs`, used identically by `compile.rs`'s own `FnCtx` and by
`proof.rs`'s `param_types_for`.)

This is a **use-site scan**, not unification: walk a combinator's body
once, and for every `Var(i)`, `i < arity`, that's ever the callee of an
application, record the argument count `k` at that call site. Two rules:

- **Consistency.** Every call site for the same `i` must agree on `k`. A
  second call site with a *different* argument count fails the whole
  scan (`None`) — this is the entire reason "a variable applied with
  inconsistent arities across call sites" is out of the fragment (see
  section 6.3): there is no way to assign `i` a single `Γ(i)` that's
  correct at both sites, and this system has no notion of arity
  polymorphism to reconcile them.
- **Default.** `Γ(i) = None` (`Int`) for any `i` never used as a callee —
  including `i` never mentioned at all, and `i` read only as a plain
  value. There is no dedicated "closure value, never called" type; an
  unapplied closure-typed parameter is classified `Int` by this pass and
  only escapes that at actual use sites that denote it directly as `Γ(i)`
  regardless (see the `Var` rule in section 4 — the *typing judgment*
  trusts `Γ` as ground truth once computed, it doesn't re-derive it).

The scan recurses into `If` branches, a self-call's own arguments, and an
ordinary application's own arguments; it does **not** recurse into a
registered combinator's own body (a literal lambda or self-recursive
value found as a plain value, or a callee position it doesn't recognize,
stops the walk without failing it) — one of the two structural reasons
(with `compile::peel`'s own folding, section 3.2) that "a capture that's
itself a capture" never arises; see `proof.rs`'s own module docs for the
full argument.

### 3.2 `compile::peel`

Not itself part of the type system, but a precondition every rule below
assumes: `peel(h)` strips a leading `Rec` (if any) and then every
*consecutive* `Abs` layer, giving `(arity, body, is_rec)`. Consecutive
layers are always folded into **one** combinator — `\a b. \c. e` and
`\a b c. e` are the same term after peeling, arity 3. This is why a
"returns a further closure" shape (the entire premise of over-application,
section 4.5) can only ever arise when `body`, once peeled, is something
other than a bare `Abs` — an `If` between two literal lambdas, most
commonly, since a bare nested `Abs` would already have been folded in.

## 4. The typing judgment

Written `Γ ⊢ e : τ`, read "with parameters (and, where noted, captures)
typed by `Γ`, `e` denotes a value of type `τ`". This is the judgment
`proof.rs`'s `denote_closure` / `denote_closure_typed` /
`denote_with_placeholders` all implement — three separate Rust functions
for three different call contexts (a standalone main term; a self-call
argument; a leaf's own expression with self-call occurrences replaced by
induction placeholders), but the *same* rules, checked identically in
each (each function's own doc comment cross-references the other two for
exactly this reason). The return value's `Denoted::Int(_)` vs.
`Denoted::Clo(_)` tag *is* the derived `τ`; there's no separate "type"
value anywhere, the tag on the elaborated kernel `Expr` doubles as it.

`compile.rs` has **no corresponding judgment**. It compiles by term
*shape* (is this node an `If`, an `App`, an `Abs`?), consulting `Γ` (its
own `ctx.closure_arities`) only to decide a call's *calling convention* —
`call_indirect` through a variable vs. a static `call` to a registered
combinator, and which `apply_k` arity to use. It never asks "does this
subterm denote `Int` or `Clo`" the way `proof.rs` must, because every
value is a plain `i64` at the compiled level regardless of type — `Int`
and `Clo` (a packed env-pointer/table-index pair) are laid out
identically, 8 bytes, indistinguishable at the machine level. `compile.rs`
is untyped by construction, not incidentally; see section 6.1.

### 4.1 Base cases

```
Γ ⊢ n : Int                                         (Lit)

Γ(i) = τ
─────────                                           (Var)
Γ ⊢ i : τ
```

`Var` covers both a combinator's own parameter (`i < arity`) and a
captured free variable (`i ≥ arity`, resolved against the *capturing*
scope's own `Γ`, not the combinator's — see section 5): both read the
same way (`Combinators`'s own docs: "either resolves the same way").

### 4.2 Arithmetic and branching

```
Γ ⊢ a : Int   Γ ⊢ b : Int
──────────────────────────                          (Prim)
Γ ⊢ a ⊕ b : Int

Γ ⊢ c : Int   Γ ⊢ t : τ   Γ ⊢ e : τ
────────────────────────────────────                (If)
Γ ⊢ (if c then t else e) : τ
```

`If`'s condition is always `Int` (`compile_cond` additionally requires it
be a *direct comparison* — `Lt`/`Le`/`Eq` — wherever the branch is used to
gate recursion structure, a stricter requirement than typing alone, see
`compile.rs`'s/`proof.rs`'s own docs). The two branches must derive the
*same* `τ` — both `Int` (`ite_ref : Int -> Int -> Int -> Int`, eager,
`ArithPostulates::new`) or both `Clo` (`ite_clo_ref : Int -> Clo -> Clo ->
Clo`, lazily postulated, primed once per `build_universal` call so its
first use is never inside a truncating `params_and_close_typed` scope —
see `proof.rs`'s own docs on that staleness class). One of each is
rejected (`an_if_mismatching_int_and_clo_branches_is_out_of_scope`) — this
system has no sum/union type to reconcile them, only these two
uniformly-typed constructors.

### 4.3 A literal lambda as a value

```
h a literal lambda (or self-recursive value), own arity k > 0
───────────────────────────────────────────────────────────── (Abs/Rec-value)
Γ ⊢ h : Clo_k
```

Always accepted regardless of what `h`'s own body does (`register`/
`mk_clo_ref`/`combinator_value` never denote it) — a call *through* this
value is what's actually typed, at whichever later use-site applies it,
by the rules below.

### 4.4 Calling a variable

```
Γ(x) = Clo_k   Γ ⊢ a_1 : Int  ...  Γ ⊢ a_k : Int
──────────────────────────────────────────────────  (Var-App)
Γ ⊢ x(a_1,...,a_k) : Int
```

Every argument, and the result, is `Int` — `apply_ref(k)`'s own postulated
type is `Clo -> Int -> .. -> Int` unconditionally (`k` copies of `Int`),
regardless of what `x`'s own real parameter types are. This is a genuine
loss of precision compile.rs's own `call_indirect` dispatch already has
(its docs: "per compile.rs's own typed dispatch, arguments are always
`Int` regardless of the callee's own signature") — a closure that
actually expects a `Clo`-typed argument, called through a variable, is
outside this fragment's own expressiveness entirely, not merely
unverified. A self-call (`x = Var(self_idx)`, `k = arity`, tail or not)
follows the identical shape but is never routed through `apply_ref` at
all — its result is `Int` by this whole fragment's own founding
convention (every provable recursive function computes an `Int`), not
because anything computes it as such.

### 4.5 Calling a literal lambda: exact, under-, and over-application

```
h peels to (n, body, _)   Γ ⊢ a_1 : T_1  ...  Γ ⊢ a_n : T_n
(T_i from param_types_for(h), h's own i-th declared parameter's type)
ρ = combinator_return_type(h)   (§4.6; None defaults to Int)
──────────────────────────────────────────────────────────── (LitLambda-Sat)
Γ ⊢ h(a_1,...,a_n) : ρ
```

`call_ref(h)`'s own postulated type is `T_1 -> .. -> T_n -> R` (`R = Clo`
iff `combinator_return_type(h)` says so, `Int` otherwise — this is new;
`R` used to be hardcoded `Int` always, see section 6.2's own history).

```
h peels to (n, body, _)   0 < k < n
Γ ⊢ a_1 : T_1  ...  Γ ⊢ a_k : T_k       (T_i from h's own first k params)
─────────────────────────────────────── (LitLambda-Under)
Γ ⊢ h(a_1,...,a_k) : Clo_{n-k}
```

Real partial application, resolved at compile time (`pap_ref`, `k == 0 ||
k >= n` rejected outright — `pap_ref`'s own guard, section 3 above) —
`compile.rs`'s own `register_partial_app`/`emit_pap_wrapper` counterpart.

```
h peels to (n, body, _)   m > 0
Γ ⊢ h(a_1,...,a_n) : Clo     (LitLambda-Sat, §4.5, must derive Clo)
Γ ⊢ a_{n+1} : Int  ...  Γ ⊢ a_{n+m} : Int
──────────────────────────────────────────  (LitLambda-Over)
Γ ⊢ h(a_1,...,a_{n+m}) : Int
```

Over-application: `h`'s own saturated call is typed first (exactly the
rule above), and only when it derives `Clo` is the result dispatched
through `apply_ref(m)` on the extra `m` arguments — the *same* rule as
`Var-App`, just with the callee freshly computed rather than read from
`Γ`. A saturated call that derives `Int` makes `LitLambda-Over` simply
not apply — `h(a_1,...,a_{n+m})` has no derivation, the term is outside
the fragment (`compile.rs` itself has no such check at all, see 6.1).

### 4.6 `combinator_return_type`: a second, smaller judgment

`LitLambda-Sat`'s `ρ` isn't looked up in `Γ` (there is no `Γ` for a
combinator's own *result*, only for its parameters) — it's *derived*, by
a structurally separate judgment, `combinator_return_type`/
`return_type_of` (`proof.rs`), over `h`'s own peeled body, in `h`'s own
freshly-computed `Γ_h = param_types_for(h)`:

```
Γ_h ⊢ n : Int                                            (Lit)
Γ_h(i) = τ  (i < h's own arity)                           (Var, in range)
i out of range for Γ_h                 ⟹  undetermined    (Var, capture/self)
Γ_h ⊢ a : Int, Γ_h ⊢ b : Int           ⟹  Int             (Prim)
Γ_h ⊢ t = Γ_h ⊢ e = τ                  ⟹  τ               (If)
a self-call, any arity                 ⟹  Int             (Self-App)
calling a Var (parameter or capture)   ⟹  Int             (Var-App)
h' a literal lambda, exactly saturated ⟹  combinator_return_type(h')
h' a literal lambda, under-applied     ⟹  Clo             (PAP value)
h' a literal lambda, over-applied      ⟹  Int             (dispatched result)
h' bare, as a value (Abs/Rec)          ⟹  Clo
```

This mirrors section 4's own rules almost exactly (deliberately — it's
"what would `denote_closure` return here, without building any `Expr`"),
with one simplification: a captured free variable's *own* type is never
needed, because calling *any* closure value — parameter, capture, or
(recursively) another combinator's own saturated result — is `Int` either
way (`Var-App`/the recursive case both collapse to the same answer
regardless of which it is). This is also what makes the recursion
well-founded without memoization: a self-call is `Int` by convention
(never needs `h`'s own answer to compute `h`'s own answer), and calling a
*different* literal lambda `h'` recurses into a distinct, already-built
term — hash-consing means a term can only reference an *already-existing*
sub-hash, so the "which combinator calls which" relation is a strict
partial order matching construction order and can't cycle back to `h`.

`None` (undetermined — the shape isn't recognized) is `call_ref`'s own
historical, always-sound fallback: `R` in `LitLambda-Sat` above defaults
to `Int`. A genuinely `Clo`-returning body this judgment fails to
recognize just misses the widening, the same "sound, not complete"
tradeoff the rest of this fragment already makes everywhere.

## 5. Captures

A captured free variable's type is **not** looked up against the
combinator that captures it — it's looked up against the *capturing*
scope's own `Γ` (`capture_sig(captures, Γ)`, `proof.rs`), since a
captured index is always relative to "the one flat ambient scope
currently being denoted" (its own module docs) — never, transitively, to
that scope's *own* captures (architecturally impossible, section 3.1).
`γ_i = Γ(captures[i])`, and the environment type `Env_γ` (with
constructor `mk_env_γ : T_1 -> .. -> T_n -> Env_γ`, `T_i = Clo` iff `γ_i`)
is postulated once per distinct signature `γ` — not per combinator, not
per arity alone; two combinators with the same *typed* capture shape
share one `Env`.

## 6. What this formalization actually finds

### 6.1 `compile.rs` is untyped; `proof.rs`'s typing is the real trust boundary — for structure

`compile.rs`'s own soundness doesn't rest on any rule in section 4 at
all: it rests entirely on `jit.rs`'s external, sample-based verification
against the interpreter. Nothing above is checked while compiling — an
over-application of a plain `Int`-returning function, for instance, still
compiles (into a `call_indirect` on a garbage table index that traps or,
astronomically unlikely, lands on some unrelated entry), exactly as
`compile.rs`'s own "Over-application" docs describe; `LitLambda-Over`'s
precondition is enforced *only* on `proof.rs`'s side, because only
`proof.rs` needs a `τ` to build a well-typed kernel `Expr` with. This
asymmetry — one side type-erased and externally verified, the other
type-directed and internally checked — is why `proof.rs` needed an actual
(if scattered) type system and `compile.rs` never did.

### 6.2 The kernel-checked proof doesn't actually verify arity

This is the sharpest finding from writing the system down as one thing:
**`Clo` is a single, arity-blind kernel type** (section 2). Every rule in
section 4 that involves a `Clo` value — `Var-App`'s `apply_ref(k)`,
`LitLambda-Sat`'s own parameter types, `LitLambda-Over`'s dispatch,
`Capture`'s `Env_γ` — gets its arity from **Rust-level bookkeeping**
(`Γ`, `param_types_for`, `capture_sig`, `combinator_return_type`), never
from anything the kernel itself inspects. `kernel::check`ing the resulting
proof confirms the *elaborated expression* type-checks against `Int`/
`Clo`/`Env_γ` as postulated — it does not, and structurally cannot,
confirm that the `k` baked into `apply_ref(k)`'s own postulate actually
matches the real arity of whatever `Clo` value flows through it at
runtime. That agreement is established entirely by the Rust code building
the proof being correct, checked by this project's own tests (unit tests,
three fuzzers, `debug_assert_has_type`) — not by the kernel-checked proof
itself. It's a real, working safety net (this whole session's `push_pap_env`
and `ite_clo_ref` bugs were both caught by it), but it's a different kind
of guarantee than "the kernel verified this," and the project's own
framing ("checked, not just asserted") is, on this one point, narrower
than it reads: checked that the *structure* agrees, assuming arities
already line up; arity itself is asserted, by Rust, not checked, by the
kernel.

### 6.3 Every "still out of scope" case traces to a specific missing rule

- **A variable applied with inconsistent arities** (`compile.rs`'s last
  open restriction): no rule in section 3.1 can assign one `Γ(i)` correct
  at two different arities; the fragment has no arity polymorphism.
- **A genuinely higher-order top-level result**: `prove_closure_expr`'s
  own entry point hardcodes the top-level judgment as `Γ ⊢ body : Int`
  (`.int()?` at its own call site) — there is no rule permitting `Γ ⊢
  body : Clo` at the outermost level, only at and beneath section 4's
  own internal rules.
- **A capture of a capture**: not a missing rule at all (section 3.1,
  section 5) — the shape can't arise given how `Γ` is scoped and how
  `peel` folds consecutive `Abs`.

## 7. A desired type system: arity-indexed `Clo`

The one change section 6.2 suggests: replace the single postulated `Clo :
Sort(0)` with a family `Clo_k : Sort(0)`, one per arity actually used
(mirroring how `Env_γ` is *already* postulated per signature, not
universally) — `param_types`/`callee_param_types` already carry the `k`
needed to pick the right member of the family at every existing call
site, so this is a change to *which* postulate `clo_ty()` returns, not a
new inference pass. `apply_ref(k) : Clo_k -> Int -> .. -> Int` would then
make the kernel itself reject a `Clo_j` value, `j ≠ k`, supplied where
`Clo_k` is expected — closing the exact gap section 6.2 identifies, for
the parts of the fragment already tracking `k` correctly in Rust.

What this *doesn't* buy: none of section 6.3's three restrictions move.
Arity-indexing makes the *existing* guarantee genuinely kernel-checked
instead of Rust-asserted; it doesn't add arity polymorphism (still no
rule for an inconsistently-called variable), doesn't add a top-level
`Clo` result (a separate, deliberate restriction, not a typing gap), and
doesn't touch the capture-of-a-capture non-issue at all. It's a
soundness-depth improvement, not a coverage improvement — genuinely
worth doing on its own merits, but a materially different, separate piece
of work from every widening this session has otherwise done.
