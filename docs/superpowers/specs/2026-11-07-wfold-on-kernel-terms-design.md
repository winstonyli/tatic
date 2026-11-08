---
status: draft
---

# The width-free fold on kernel terms (w1)

Item w1 of the 2026-11-07 session moves `uniform/wfold.rs` and `uniform/wnat.rs` off the named, unshared tree `T`
(`uniform/width.rs`) and onto the kernel's interned `Expr`. The facts come from three sources: a read-only survey, the x2 spike, and
adversarial reviews of this spec. Each claim was checked against the code at b52c265. Measurements are kept in `docs/tier-cycle/`, under
"One generator proves stream laws at all widths", in its paragraphs "Where a sweep's time goes" and "A port spike on kernel terms".

## Intent

The wfold sweep proves sampled pairs of equal two-level terms at every width. Most of its cost is building the proofs, not checking them.
In the 1-in-97 sample, `Law::proof` took 83% of busy samples and the kernel check 10%. Two things cause this:

- **Representation.** A `T` is a tree with no sharing, lowered to `Expr` by name lookup (`width::comp`). Each repeated table, step and
  motive is built, copied and lowered again.
- **Algorithm.** `by_cases` calls its `lr` closure at every node of a 2^nv case tree, and each call rebuilds every table at full size.

The x2 spike fixed the second cause, but only for the tables and side lemmas. It cut the sample from 178.0 G to 39.1 G retired
instructions. x2's profile reports these shares of busy samples, and they overlap:

| Part | Share |
|---|---|
| `wnat::ind` | 35% |
| `good_carries` (inside `wnat::ind`) | 24% |
| lowering | 18% |
| kernel check | 23% |

If the check stays at x2's level, about three quarters of the 39.1 G is left for the port to remove. The check may also fall: when x2
changed the term shape, it went from about 17.8 G to about 9.0 G. Those two figures are inferred from shares of different runs (10% of
178.0 G and 23% of 39.1 G), not measured directly.

This spec moves the fold off `T` entirely. Each term is then interned once per pair, and each builder runs once per use rather than once
per case-tree node.

## Goals

- `wnat.rs` and `wfold.rs` build `Expr`. Under c1, naming `T` in either file is a compile error.
- No builder in `wnat.rs` or `wfold.rs` computes a de Bruijn index by hand or relies on a reserved free name. `StepProof` and `lemma_n`
  keep their own indexed builders. Examples of such names today: `$f`, `$ih`, `$w`, `$mm`, `$hj`, `$hn`, `X`, `m`, `g`, `$P`, `$ht`,
  `$hf`, `_r`, `_t`, the names in the `XS`, `GS`, `CB` and `CG` tables, and the stage proofs' locals.
- One proof-step builder serves both `machine.rs#tree_proof` and the fold (b1).
- The proofs stay accepted, and every control still fails: a flipped table bit (`w_fold_a_false_table_is_rejected`), a statement with
  the wrong right side (`w_fold_add_associates`), a theorem instantiated at the wrong bit (`w_fold_a_theorem_applies_to_good_streams`),
  and swapped comparison operands (`w_fold_a_comparison_is_its_own_law`). The theorem-application test grows to pin the statement's
  layout (Checks).

## Non-goals

- The Church-indexed families stay on `T`: `bitwise.rs`, `mul.rs`, `shift.rs`, `symmul.rs` and `symmul_stream.rs`. `PARKED.md` ("Delete
  the hand-written law families for the width-free fold") deletes them once a bridge from a W-indexed theorem to `Bv_n` exists, so porting
  them now would mean writing code only to delete it. `T` and `width.rs` (including its `rew` and `cases2`) stay for them.
- No new proof shapes. The fold, the encoding, the induction and the statement stay as they are; only how they are built changes.
- Proof terms need not be `Expr`-equal to today's, and cannot be. `table_app`'s tables are reduced decision diagrams, today's are full mux
  trees, and the two are not convertible on symbolic bits (`mux c a a` is not `a`). Acceptance and the controls are the check.
- No speed target. The verdict is a retired-instruction count (Checks), and no timed run is needed.

## Design

### Builder: `Cx` and `At`

`Cx` holds the binder depth. `Cx::lam(ty, |cx, x| body)` binds a variable and passes it to the body as an `At`, which is a term plus the
depth it was made at. `cx.at(a)` shifts an `At` to the current depth, and `cx.mark(e)` makes an `At` from a term at the current depth.
Shifting a closed term is free, because `shift` returns its input when nothing is loose.

- **Home.** `Cx` (with its methods), `At`, `Ty`, `tele`, `law` and the `ty!` macro move from `src/wasm.rs` (lines 13-73, about 60
  lines) to `encoding/cx.rs`. `encoding.rs` re-exports them; the macro goes through `pub(crate) use ty;`, and `tele` becomes
  `pub(crate)`, since `wasm.rs` also calls it.
  - A new `statement(tys, stmt)` returns `law`'s statement alone, for tests that build one by hand. `law` is rebuilt on it, so the Pi
    telescope is written once.
  - The reason to move them is dependency direction: they are a generic builder, `wasm.rs` is one consumer, and the fold should not
    depend on the target-machine model. A visibility change alone would also compile.
  - `uniform/symmul_stream.rs` has an unrelated private `struct Cx`; it is left as it is.
- **One new binder form, `Cx::under`.** `sigma`'s body, `wty`'s body, `pair`'s family and `wrec`'s children family all sit under a
  binder without a lambda around them.
  - A public `Cx::under(|cx, x| body) -> Expr` covers all four, for example `sigma(a, cx.under(|cx, x| ..))`. It is the private `bind`,
    made public.
  - The `sigrec` and `wrec` motives are lambdas and use `Cx::lam`.
  - A body that does not depend on its binder, such as the invariant's nested `sigma`s, is still built inside `under`. It ignores the
    variable and reaches outer terms through `cx.at`; it is never passed unshifted.
- **Depth check, always on.** `Cx::at` subtracts with `u32`, so going below the birth depth panics only when overflow checks are on. It
  becomes `checked_sub(..).expect(..)`, so release-profile runs catch the error too.
- **Two roots.** A pair builds two roots: the proof and the statement (a1). Open terms stay inside the root that made them. The statement
  root rebuilds the root streams with the same `side` function.

### Shared step builder (b1)

`tree_proof` already builds every piece of the fold's per-position step on `Expr`, as closures over its machines and encoding:

- `phi_expr` and `g_expr`: `table_app` over the encoding's tables.
- `step_of` and `side_f`: `Machine::step` with `GoodOps` and dummy witnesses.
- The leaf memo `step_at`: each leaf's step and phi values, shared by a side's `m + 1` lemmas.
- The side lemmas: `lemma_n` over `k + c` bits. The `None` path builds the statements and the `Some` path the leaves.
- `eq`: `cong_n` over an `m`-ary `fmap`, the `sym` of one side's lemma, and two `trans_proof`s.

wfold's `Law::step`, `f`, `phi`, `g`, `lemma` and its `eq` closure are the same objects, built on `T` and without the leaf memo. They
become one struct in `machine.rs`:

```rust
StepProof<'a> {
    machines: &'a [Machine; 2],
    enc: &'a Encoding,
    k,
    gops: GoodOps,
    steps: RefCell<HashMap<(usize, Vec<bool>), Step>>,
}
```

- **`Step`.** The `Rc<(Expr, Vec<Expr>, Vec<Expr>)>` alias moves from inside `tree_proof` to module level. `m` is `enc.phi[0].len()`
  and a side's carry count is `machines[side].carries()`, both derived on use. `step_at`, the memo's accessor, is a private method.
- **Methods.**
  - `phi(side, j, s)` and `g(j, v)`: the `table_app`s.
  - `step_of(side, v: &[Expr]) -> (Expr, Vec<Expr>)`: a side's step at symbolic operand and carry values, with dummy witnesses.
  - `side_f(side, j, v)`: the output for `j = 0`, else phi `j - 1` of the next carries.
  - `lemma(side, j) -> (Expr, Expr)`: the closed side lemma `F_j = G_j` over `k + c` bits and its type, by `lemma_n`. Its leaves go
    through `steps`, so a side's `m + 1` lemmas share each leaf's step.
  - `eq(j, lem: [&Expr; 2], ug: &[Gb], st: [&[Gb]; 2], ip: &[Expr]) -> (Expr, Expr, Expr)`. It takes the two sides' lemma proofs for `j`,
    the operand bits with witnesses (`ug`), each side's carries with witnesses (`st`) and the proofs that the phi values agree (`ip`). It
    returns side 0's value, side 1's value, and a proof that they are equal.
- **Callers own the lemmas.** `tree_proof` wraps each `lemma(side, j)` in `shared_lemma` with today's key (machine key, `k`, `nv`,
  `F{j}` and `enc.g[j]`, `enc.phi[side]`) and keeps the returned proof, which may be a `Postulates` parameter, as today. wfold calls
  `lemma(side, j).0` directly.
- **Visibility.** `machines` and `gops` are `pub(crate)`, so `good_carries`' `hj` can run `Machine::step` with real witnesses.
- **Lifetime.** A `StepProof` is borrowed and lives only for one `tree_proof` call or one `proof` call. `GoodOps::new` is three `good2`
  calls, so building one per call is cheap. wfold gets the leaf sharing it lacks today through `steps`.
- **Not shared.** wfold's `agree` (the `m` phi equations at given carries, for the invariant and `hj`) is a two-line map over `phi` that
  `tree_proof` never uses, so it stays in `wfold.rs`.
- **Cleanup.** The stale "and its P lemma" in `step_at`'s comment goes.

### Index and streams (`wnat.rs`)

- **Closed constants.** `encoding::constant` keeps its `build: fn() -> Expr` argument but drops the hand-numbered slot. Today slots 0-5
  are in `gates.rs`, 6-7 in `division.rs` and 8 in `good.rs`, and nothing checks for collisions.
  - The memo is keyed by `build as usize`, the function's address. A non-capturing closure coerces to `fn()`, and a capturing one does
    not compile, so one call site cannot memoize two values. If the linker folds two identical functions, they build equal terms, which is
    harmless. The key stays a `usize`, which the `Fx` hasher handles in one round.
  - The nine existing call sites drop their numbers, and `job.rs`' text for `CONSTANTS` changes from "by slot" to "by build function".
  - `constant` becomes `pub(crate)`. wnat's constants use it: for example `tag_ty`, `nw`, `bw`, `unit`, `star`, `empty`, `zero_w`,
    `carry_fn`, `add_fn`, `shl_fn` and `mul_fn`.
  - Parameterized builders (`shl_fn(fill)`, `mul_fn(fill)`) memoize `fill = false` through a fn item. The `fill = true` mutant is built
    directly.
  - This adds no `thread_local`. With one region per pair, each constant is built once per pair. If codegen gives one closure two
    addresses (two codegen units), the constant is built twice, to an equal interned term: a rebuild, not an error. The existing
    once-per-generation test runs at test opt-level, where this does not arise.
- **Builders over operands** take `&mut Cx` and either `At`s or `Expr`s at the current depth. Examples: `carry`, `add`, `shl`, `eqb`,
  `maybe`, `just`, `goodmaybe`, `good_stream`, `carry_at`, `succ_w`, `rec_w`, `shr`, `tmask` and `xor3`.
  - `carry`, `add` and `shl` apply the closed function constants.
  - `good_case` goes. Its two callers, `zero_w` and `succ_w`, build closed tags, so the two tags become constants, `zero_tag` and
    `succ_tag`. Each inlines `good_case`'s `\P hj hn.`, with `hn` or `hj star` as the body. `zero_w` and `succ_w(cx, n)` add only the
    `Sup` and its child lambda.
- **One tag split.** `rec_w`'s `sel` and `ind`'s `selm` build the same term: the tag's case split on `m`, where the `just` case continues
  with `f w`. Every continuation uses `w` only through `f w` and `ih w`.
  - A plain struct `Tag { x_ty, m, f, ih }` of `At`s holds what the split needs. `rec_w` and `ind`'s leaf each build one.
  - `tag_case(cx, &Tag, k, z)`, with `k: Fn(&mut Cx, Expr /* f w */, Expr /* ih w */) -> Expr`, binds `w` and applies `f` and `ih`
    itself. `w` never leaves it.
- **Proof combinators.** wnat's `sym`, `trans` and `cong3` give way to the kernel's `sym(a_ty, x, y, p)`, `trans_proof(a_ty, x, y, z,
  p, q)` and `cong_n(a_ty, b_ty, f, xs, ys, ps)`, with `bool0()` as each type.
  - Five of wnat's 11 `rew` calls are inside those three helpers and go with them. wfold's one `rew` is in `cong`, which `StepProof::eq`
    replaces.
  - Six `rew` sites remain in the stage proofs, at wnat lines 253, 262, 307, 316, 334 and 352. With `p : l = r`, each family has the shape
    `\t. eqb(F(t), C)` or `\t. eqb(C, F(t))`:
    - The first shape becomes `trans_proof(bool0(), F l, F r, C, cong1(bool0(), bool0(), F, l, r, p), h)`. When the base is `rfl`, it
      is `cong1(bool0(), bool0(), F, l, r, p)` alone, which needs `F r` to be `def_eq` to `C`: by computation at 253 and 262 (`maj`
      and `xor3` of the zero stream and `ff`), syntactically at 334.
    - The second shape (line 352) becomes `cong1(bool0(), bool0(), F, r, l, sym(bool0(), l, r, p))`.
  - `F` is `cx.lam(bool0(), ..)`, and `F l`, `F r` and `C` are built explicitly. No `rew` is written on `Expr`.
  - `cases2` has two uses, both in `proof_add_comm`. Under d1 it becomes a 10-line `Cx` function in `wnat.rs`. `width.rs`' copy stays
    for the families' six uses, so the two copies get a `PARKED.md` entry, triggered by the families' deletion, in the commit that
    adds the `Cx` one.
- **`ind`.** The tag's internals stay inside `ind`, and the binders are described once:

  ```rust
  pub(super) fn ind(cx: &mut Cx, tele: &[Ty], body: &dyn Fn(&mut Cx, Expr /* index */, &[At]) -> Expr, target: Expr,
                    pred: &dyn Fn(&mut Cx, &Tag, &[At]) -> Expr,
                    hj: &dyn Fn(&mut Cx, Expr /* f w */, Expr /* ih w */, &[At]) -> Expr,
                    hn: &dyn Fn(&mut Cx, &[At]) -> Expr) -> Expr
  ```

  - `tele` lists the binders that bring the statement down to `Sort1`:
    - `good_carries`: `$P`, `$ht`, `$hf`, which is what `goodbool` unfolds to;
    - stage 3: `y`, `i`;
    - stage 4b: `x`, `y`, `i`;
    - the phi invariant and the other eight sites: none.
  - `ind` builds the motive as `\n. Pi tele. body(n, tele)` and the introductions as lambdas over `tele`. This replaces today's separate
    `motive` and `pre`, which write the same binders twice.
  - `ind` passes `tele`'s `At`s to `body`, `pred`, `hj` and `hn`.
  - `pred` receives the `Tag` at the abstracted `m` and calls `tag_case` on it as often as it needs. So `X`, `m`, `g`, `$f`, `$ih`, `$w`
    and `$mm` never leave `ind`.
  - `hj` has `k`'s shape plus the telescope. It receives the term `ih w`, whose type is the telescope's Pi, and stages 3 and 4b apply
    it to their next operands. Every `pred` today uses only `f w`, so it ignores `Tag.ih`.

### The law (`wfold.rs`)

- **Free functions, no `Law` struct.**
  - `encode(k, t1, t2) -> Option<([Machine; 2], Encoding)>` parses and runs `moore_encoding`, and builds no terms.
  - `proof(k, &[Machine; 2], &Encoding) -> (Expr, Expr)` builds the `StepProof` and both roots.
  - `operands(k) -> Vec<Ty>` is the telescope, in today's order: all `x_i : Bits`, then all `g_i : good x_i`, where `g_i`'s type reads
    `xs[i]`. `w_fold_a_theorem_applies_to_good_streams` relies on this order.
  - The control `w_fold_a_false_table_is_rejected` flips a bit in the returned `Encoding` before calling `proof`.
- **Sides.** `side(cx, machine, xs: &[At]) -> (Expr, Vec<Expr>)` builds a side's root and carry streams, with `k = xs.len()`.
  - Tests use it too. The swapped-operand control, which has no encoding, builds both sides through it.
  - `w_fold_a_comparison_is_its_own_law` and `w_fold_add_associates` build their statements with `statement(&operands(k), ..)`, `side`
    and `At`s. This replaces `law.over(..)`, `law.sides[0].root` and the named `x0..x2` streams.
- **The proof root.** One telescope over `operands(k)`, built with `law`. Each goodness proof and the invariant are built once, then bound
  as a typed hypothesis: `app(cx.lam(ty, |cx, h| rest), proof)`. Uses inside `rest`, at any depth, reach them through `h`.
  - The kernel infers the lambda's body once under its domain, checks the argument once against that domain, and instantiates the
    result type with the argument only where it mentions `h` (`check.rs`, `Node::App`). So each proof is checked once, provided no
    inferred type mentions a goodness proof. A test asserts that the proof's inferred type is `def_eq` to the statement and records its
    size (`term_sizes`), so a proof leaking into a type shows up as a size jump.
  - An open term used at several depths would be a different interned node at each depth, so the infer memo would miss and recheck it
    every time.
  - The sides are built inline. The final equation is built under the hypotheses. This removes `closed`, `held` and today's closed
    invariant.
- **The statement root.** It is `statement(&operands(k), ..)` over `side`'s root streams. The proof's type must be `def_eq` to it, which
  the kernel check verifies.
- **Steps.** All steps go through `StepProof`, which deletes `Terms`, `Goods`, `Good`, `gate`, `good_lams`, `pick`, `Law::step`, `m`,
  `f`, `phi`, `g`, `lemma` and the `eq` closure. `agree` becomes a free function over `StepProof::phi`.
  - `Goods.konst(b).g` becomes `\i:nw. encoding::good_bit(b)`.
  - `Terms.konst(b)` becomes `encoding::bit(b)`.
  - wfold's `T` helpers `ones`, `nat_` and `at_n` are rewritten as `Cx` helpers.
- **Witnesses of later carries.** `good_carries` keeps a placeholder for the witnesses of carries after the one being proved, with no
  check. `Machine::step` never reads them into the returned witness, and a leaked placeholder is ill-typed, so the kernel would reject it.
- **`conj`, `pair`, `projections`** become `sigmas`, `pack` and `unpack` over the kernel's `sigma`, `pair` and `sigrec`. They are renamed
  so they don't shadow the kernel's `pair`. They stay because the invariant has to cross the tag split in `Sort1`, and each phi equation
  needs all the earlier ones.
- **Tests and regions.** Tests call `tatic_kernel::check` directly, and `width::run` gets no twin. Its `[name] ACCEPTED in N ms` line is
  dropped; no doc cites it. Every caller builds and checks a proof inside one `scoped` call, which the sweep already does (x1, fd83d64).

## Decisions

Each decision's options carry its group letter: D1 is z, D2 is a, D3 is b, D4 is c, D5 is d and D6 is e. The Design above assumes
the recommended option of each (z1, a1, b1, c1, d1, e1). Answers flow in this order: D1 first, then D2 and D3, then D4, D5 and D6.
A group's "Removed" line names what the search took out of the recommended design; rejected options stay listed with their reasons.

### D1 Representation

**Searched:**
- Raw indices with no builder (z3).
- Closed lambdas everywhere, x2's shape. These cannot express the induction's open motives.
- A closed `ind` lemma over the motive. It cannot express the `Sort2` goodness motive.
- A locally nameless builder (z2): the kernel's `Free(level)` with `postulates.rs`' private `abstract_frees`, without `Postulates`'
  per-parameter `infer_open`.

Removed: nothing from z1.

Context: `T` costs two things, lowering by name and no sharing. Only an `Expr` builder removes both.

- z1 **Cx closures** (recommended): the Design above.
    - Pro: no index arithmetic, and the builder exists and serves `wasm.rs`; Con: each `cx.at` of an open term costs a shift, and every
      builder takes `&mut Cx`.
- z2 **Locally nameless**: a fresh `Free` per binder, abstracted at the binder; no depth and no `At`.
    - Pro: a term whose only free variables are `Free`s is closed, so one `Expr` serves at every depth with no shifts; Con: it exposes
      `abstract_frees` and an unchecked `Free` mint as kernel API. It costs O(body) per binder, against O(body) per use for shifts. It is
      unmeasured; prototyping `ind` under both builders would settle it.
- z3 **Raw de Bruijn**: hand-computed `var(k)` and `shift`, the way most of `encoding/` is written.
    - Con: the shift obligations (`cong`'s `fmap`, `ind`'s telescope) become hand-written indices that only the kernel checks.
- z4 **Keep T**: x2, plus memoized `K(ex(..))` constants.
    - Pro: the smallest diff; Con: `T`, `comp` and the reserved names stay live in the fold, and the induction's terms, now most of the
      cost, stay unshared.

### D2 Roots

**Searched:**
- Separate closed roots for the goodness proofs and the invariant, as today.
- Closed side functions applied to each root's operands (a3).
- Open goodness proofs reused at several depths. Each depth is a new node, so the kernel's infer memo misses and rechecks the proof at
  every use.

Removed: `closed`, `held`, the closed invariant, the beta redexes of side functions, and the cross-root `At` hazard.

Context: a side's streams are used by the goodness proofs, the invariant, the proof's equation and the statement.

- a1 **One root, bound once** (recommended): one proof root. Each goodness proof and the invariant are bound once as a hypothesis, and
  the statement root rebuilds only the root streams (Design, "The law").
    - Pro: two roots and no closed wrappers; each proof is checked once; interning shares the rebuilt root streams; Con: one beta redex per
      bound proof, which the A/B count measures.
- a2 **Separate closed roots**: today's shape on `Expr`, with each goodness proof and the invariant as a closed lemma applied to `xs ++ gs`.
    - Pro: each lemma is checked once, through the closed-term memo; Con: more roots, `closed` and `held` stay, and the sides are rebuilt
      in each root.
- a3 **Closed side functions**: `side_fns(machine, k)`, used as `apps(root, xs)` in every root.
    - Con: one beta redex per use of a side stream, far more than one per proof.

### D3 Step builder

**Searched:**
- Extracting only the per-position `eq`. That leaves `phi`, `g`, `side_f`, the leaf memo and the lemmas duplicated.
- A lemma provider callback passed to the constructor, so `StepProof` could hold the lemmas. `shared_lemma` already is that wrapper.
- `agree` as a shared method. Only wfold uses it.

Removed: the provider, the stored lemmas, and `agree` from the shared surface.

Context: after the port, wfold's step pieces would be `tree_proof`'s closures written a second time over the same `Machine::step`,
`GoodOps`, `table_app`, `lemma_n` and `cong_n`.

- b1 **Extract StepProof** (recommended): Design, "Shared step builder".
    - Pro: one copy of the step proof; `tree_proof` shrinks; the port deletes most of `Law`; wfold gains the leaf memo; Con: it changes
      `tree_proof`, which the main prover uses. So the extraction lands as its own commit, with `cargo test -p church-bv --lib` and one
      gate run passing.
- b2 **Separate copy**: port wfold's step pieces on their own.
    - Con: two copies of one proof step that must agree, with no check that they do.

### D4 Module boundary

**Searched:**
- Moving the five family files into `uniform/church/` (c4).
- A new `src/stream/` module (c2), which is a namespace with no content of its own.
- A shrinking allowlist script (c3).

Removed: nothing from c1.

Context: `width` is a private module of `uniform`, so code outside `uniform` cannot name `T`. Only `wfold.rs` imports `wnat`.

- c1 **Move to src/** (recommended): `wnat.rs` and `wfold.rs` move to `src/`, beside `machine.rs`. `lib.rs` gains `mod wnat; mod wfold;`
  and `uniform.rs` loses its two lines. A `T` in either file is a compile error, and when the families are deleted later, all of `uniform/`
  goes.
    - Pro: the compiler is the guard, for two moves and their cites; Con: `src/` gains two top-level files.
- c2 **Stream module**: the same move, into `src/stream/`.
    - Con: a new module name in the docs and tour, for the same guard.
- c3 **Allowlist script**: `scripts/check/` lists the files allowed to name `width::T`.
    - Pro: no moves; Con: one more guard, plus its `_check_check.sh`.
- c4 **Families into church/**: five moves, and `pub(crate)` becomes `pub(super)` throughout.
    - Con: more than twice the moves, for the same guard.

### D5 Stage proofs

**Searched:**
- Deleting them. That removes the need for `cases2` on `Expr`, the `fill = false` constants and the `fill = true` mutant builder.
- Keeping them on `T`. That needs a second index, which under c1 must stay in `uniform/`.

Removed: nothing, since deleting them loses the only `mul` result on the W index.

Context:
- About 285 of `wnat.rs`'s 475 lines are the o1 spike's own proofs (run `2026-11-07-o1-wnat`), unused by wfold: `mul_fn`, `tmask`, `shr`, the `fill` mutant,
  `carry_cong`, `add_cong`, `shl_cong`, `shl_false`, `carry_zero`, `add_zero`, `carry_shl`, `shl_add`, `tmask_shl`, `proof_add_comm`,
  `proof_mul_shl` and seven `w_index_` tests.
- They are the only proof that a W index folds `mul` (`docs/tier-cycle/`, "The level wall is Church's").
- `PARKED.md`'s goal D entry names commutativity of `mul` as what stays unbuilt, so they are the base for a live goal.
- Apart from `good_carries`, they are the only callers of `ind` with a non-empty telescope.

- d1 **Port stages** (recommended): they build on the same index and the same `ind`.
    - Pro: keeps the `mul` base for goal D, and tests `ind` with real telescopes; Con: about 285 more lines to port, plus `cases2` on
      `Expr`.
- d2 **Delete stages**: record in doc 15 the commit that removes them.
    - Pro: a smaller port, with no `Expr` `cases2` and no `fill` builders; Con: the W-index `mul` proof is lost, and a later `mul` law starts
      again from git history.
- d3 **Keep on T**: a second index in `T` in `uniform/`, beside the ported one.
    - Con: two indexes that must agree, with no check that they do.

### D6 Order

**Searched:** landing x2 alone as a stepping stone. It is not additive, because the port rewrites all of it.
Removed: x2's `table_body` split from the port, which does not need it because it calls `encoding::table_app` directly. The stage
itself stays listed as e2.

Context:
- x1 (the parallel sweep) is committed (fd83d64), and its full sweep passed on today's code (b52c265).
- x2 is a patch, `docs/superpowers/spikes/2026-11-07-x2-kernel-table-lemma.patch`. None of its code survives the port.
- What carries over is the lemma shape: `lemma_n` with `refl(bit(v))` leaves, which is also `tree_proof`'s shape.

- e1 **One cutover** (recommended): the patch stays as the spike's record.
    - Pro: no intermediate `T` code; Con: the 4.55x arrives only with the port.
- e2 **x2 first**: apply the patch, delete `by_cases`, `mux` and `CG`, then port.
    - Pro: later sweeps get the 4.55x at once; Con: `table` and `lemma` are written twice.

## Checks

- **Tests.** `cargo test -p church-bv --lib` passes, including every control under Goals and `tree_proof`'s tests after the b1
  extraction.
- **The statement's layout.** `w_fold_a_theorem_applies_to_good_streams` runs over three pairs whose operands are not symmetric:
  - `sub(x, add(y, z)) = sub(sub(x, y), z)`, which has carries;
  - `lt(x, y) = lt(not(y), not(x))`, a root `lt`;
  - `and(x, or(x, y)) = x`, which has no carries.

  The test works at `n = 3`. It tries every assignment of all-ones and all-zeros streams to the `k` operands, with `\i:nw. good_bit(c)`
  witnesses, at two positions: `p = 0` and the last (`n - 1` for a word, `n` for an `lt`). The proof's type is inferred once. An instance is
  formed by rebuilding that Pi chain as a lambda chain over the same domains and applying it to the streams, witnesses and position;
  `def_eq` does the beta steps. Each instance must be `def_eq` to `eqb(bit(e), bit(e))` and not to `eqb(bit(!e), bit(!e))`.
  - This pins the operands' order and the position, but not the witnesses: the statement's codomain never mentions a `g_i`, and
    instantiation checks no argument.
  - So one instance per pair, at a mixed assignment with each witness matching its operand, also goes through `tatic_kernel::check`. A
    mispaired witness then fails on its domain (`goodbool(bit true)` against `goodbool(bit false)`).
  - For a word root, `e` is bit `p` of the terms' `interp` at width `n`, with all-ones as `low_bits(n)`.
  - For an `lt` root, `e` is `(a & low_p) < (c & low_p)` per side, where `a` and `c` are the interps of the root `lt`'s two argument
    terms, as `w_fold_streams_compute_the_words` computes it.

  The mixed assignments tell the operands apart. A full `check` per instance would re-infer the whole proof each
  time, since the infer memo lasts one call; about 100 such checks would cost several times the rest of the suite. The test is timed
  once it is written, before the grid is settled.
- **Instruction counts**, per `ICOUNT.md`, on the 1-in-97 sample:
  - Both arms run the same test at `WFOLD_STRIDE=97` (in `<exe>.env`, which `Setup` reads) and `WFOLD_THREADS=1`, with x1's per-pair
    `scoped`.
  - The baseline is a worktree of b52c265 with the x2 patch applied, so x2's 39.1 G is re-counted on this loop.
  - The arms' test paths differ (`uniform::wfold::..` and `wfold::..`), so the filter matches by substring, without `--exact`.
  - Run an A/A first. The exe uses mimalloc with large pages, so rotate the arms across batches of 4 or more, and compare medians with
    max/best beside them.
  - Report the build span. Subtract each arm's count at the largest stride that still samples one pair with an encoding: the test asserts
    `tried > 0`, and `icount.ps1` stops on a failure. That count is the enumeration's fixed cost plus one pair.
  - Confirm the verdicts (469 tried, 1 with no encoding, pass) from a separate untimed `--nocapture` run, since the counted run drops its
    output.
- **Full sweep.** `WFOLD_STRIDE=1` and `WFOLD_THREADS=10` through `run.ps1` give 45621 proved and 56 without an encoding.
- **The c1 guard.** A planted `use crate::uniform::...` of `T` in `src/wfold.rs` fails to compile.
- **Docs and guards.** `docs/TOUR.md` is updated, and every `scripts/check/` guard named in `CLAUDE.md` passes: `tour_check.sh`,
  `cite_check.sh`, `size_check.sh`, `test_placement_check.sh`, `layout_check.sh` and `front_matter_check.sh`.

## End-state fit

- **`encoding/cx.rs`** (new): `Cx`, `At`, `Ty`, `tele`, `law` and `ty!`, moved from `wasm.rs` (about 60 lines). It adds `statement`,
  `under` and the checked depth. `wasm.rs` imports them.
- **`encoding/gates.rs`:** `constant` becomes `pub(crate)` and is keyed by its build function's address; slots 0-5 go.
- **`encoding/division.rs`, `good.rs`:** their slot numbers (6, 7 and 8) go.
- **`job.rs`:** the `CONSTANTS` line of `THREAD_LOCAL` reads "by build function".
- **`machine.rs`:** `StepProof` (b1) and the module-level `Step` replace `tree_proof`'s `phi_expr`, `g_expr`, `step_of`, `side_f`,
  `steps`, `step_at`, the side-lemma body, `lemmas` and `eq`.
- **`src/wnat.rs`**, moved from `uniform/` (c1), is on `Expr`.
  - It deletes its `T` builders, the `K(ex(..))` wrappers, `sym`, `trans`, `cong3`, `sel`, `selm`, `fw`, `good_case`, `noop` (today's
    `pre` identity), the `rew` uses and the reserved names. `stream_of`, `num`, `zw`, `ptw` and the `tag_*` builders are ported.
  - `ind` takes `tele` and `body`, and `Tag` with `tag_case` is the one tag split. `zero_tag` and `succ_tag` are constants.
  - `cases2` (d1) is written over `Cx`.
- **`src/wfold.rs`**, moved from `uniform/` (c1), is on `Expr`. It deletes:
  - the `Law` struct and its methods;
  - `Terms`, `Goods`, `Good`, `gate`, `good_lams` and `pick`;
  - `p_of`, `mux`, `table`, `by_cases` and `cong`;
  - `over`, `closed`, `held`, `XS`, `GS`, `CB` and `CG`;
  - the `Side` struct and the closed invariant.

  `encode`, `proof`, `operands`, `side` and `agree` replace them. The file's header comment, which describes `ind`'s `pre` and the q2
  spike, is rewritten.
- **`uniform.rs`:** `mod wfold;` and `mod wnat;` go.
- **`uniform/width.rs`:** the `W`, `Sup` and `WRec` variants of `T` go, since only wnat builds them. So do their `comp` arms: removing `W`
  collapses the merged `Pi | Lm | Sig | W` arm and its inner match. `Sig`, `Pair` and `SigRec` stay for the families. The rest of
  `width.rs` and the families are unchanged.
- **`uniform/mul.rs`:** `bit_of` stays for the families. Its five uses in wnat and wfold become `encoding::bit((val >> j) & 1 == 1)`.
- **Docs and comments that name the old paths:**
  - doc 15: the sections "One generator proves stream laws at all widths" (the port's counts and the new paths) and "The level wall is
    Church's";
  - `PARKED.md`: the goal D entry, and the family-deletion entry, which cites `uniform/wfold.rs` and should now say that `T` serves only
    the families;
  - `docs/TOUR.md`: wnat and wfold leave the `uniform/` line and appear at top level, along with `encoding/cx.rs` and `StepProof`;
  - code comments: `uniform/mul.rs` (two mentions of `wnat.rs`) and `crates/tatic-kernel/src/postulates.rs` (`uniform/wnat.rs`).

  `docs/superpowers/specs/2026-09-30-bitvector-interface-design.md` also cites `uniform/wnat.rs`. It is a finished spec and is left as
  history.

## Left to the plan

The commit order follows from wfold depending on wnat's items:

1. Move `Cx`, and add `statement`, `under` and the checked depth. The tour's `encoding/` line gains `cx`.
2. Key `constant` by its build function.
3. Extract `StepProof` from `tree_proof` alone (b1), with the gate run. The tour gains `StepProof`.
4. Port wnat and wfold together, with the stage proofs under d1 and the dead `T` variants removed. This is one commit because a wfold on
   `T` cannot compile against a wnat on `Expr`, and a bridge between them would be a shim. Inside the working tree, wnat's `w_index_`
   tests pass first, before wfold is ported. Both files import by name from the start (no `width::*` or `wnat::*` globs), and the
   `cases2` `PARKED.md` entry lands here.
5. Move the modules under c1: `git mv` plus the `lib.rs` and `uniform.rs` lines, and the docs that name the old paths.

Each commit passes its tests and the guards under Checks.
