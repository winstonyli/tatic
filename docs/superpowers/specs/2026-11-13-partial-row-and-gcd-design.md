---
status: active
---

# The partial row, and gcd through the gate

## Intent

`gcd` (`rec f a b = if b == 0 then a else f b (a % b)`) and `gcd_with_two_base_cases` are the census rows the gate
leaves `NotCovered` for want of a `%` row (`proof/tests/gate.rs#what_cps_cannot_take_is_not_covered`, "gcd (Mod)"):
remainder by zero has no value (eval errors, wasm traps), so `%` has no machine row. The decision of 2026-11-10
(`docs/decisions/2026-11-10-v08-shape-and-any-backend.md`, "Decided: division and remainder by zero") made remainder a
*partial row*: outside its domain the machine answers the statement's no-value answer `z`, the gate's source side
emits the same guard, and eval's error and the row's domain read one definition. The same file's "Open: where the
domain lives" records the placement picked on 2026-11-13: the domain on the row in `tatic-wasm`, the table cached
there, eval reading the domain through the row, and a domain on every row (constant true on the total ones) rather
than an 8th constructor, with guards on Word sites only; the next section records how the guard reaches the walk.

That the missing row is the only blocker was confirmed by the spikes: with the `mod` row and the guard, both gcds are
`Accepted` and no other `VERDICTS` row changes (doc 15, "The gate's branch step made linear (2026-11-13)").

Done when: both gcd rows are `Kind::Accepted` in `proof/tests/baseline.rs#VERDICTS`; `print_verdict_rows` shows every
other row unchanged; `mod` is checked at b = 0 by the table test against wasmtime; the gate's linear-work tests pass,
including the `if` chain and the nested `%` chains; at the plan's close, the ignored `tatic-wasm` and `tatic` proof
suites and church-bv's default tests (`hidden_state_is_classified`) pass.

## Decided: every Word guard through the walk's probe (2026-11-13)

Picked 2026-11-13, after three spikes (doc 15, "Word-row guards through the probe: a spike (2026-11-13)" and
"The gate's branch step made linear (2026-11-13)"), as "option 1" of those docs: every Word site is guarded on both
sides through `self.choose`
(the probe `CH` in the walk, the real choice in the statement), never folded, with `z` as the else branch, and the
walk gains one last-resort `refl` rule. Bit rows carry `TOTAL` and are not guarded.

Why it holds now: the walk's step over a branch cost work proportional to the rest of the program (main's own `If`
chains grew 2.3x to 3.6x per doubling of depth), so guarding every Word site made the check grow about 3x per doubling.
`5b062ee` made that step linear (`sim.rs#cong_lemma` applied, `machine.rs#choose_fn` applied); on top of it this design
accepts both gcds and keeps every series linear (section 7). What it costs: a constant factor on Word-heavy code
(`doubling(12)` check 4.0x main), accepted.

Facts the design rests on (checked in the code and the spikes):
- The machine's guard sits in a constructor meaning (`machine.rs#interp`) shared by every site; `ctor_ty` abstracts
  only `F : Sort2 -> Sort2`, so no per-site guard combinator can be an operand. What varies per site is the domain
  operand. So a total site's guard cannot be dropped on the machine side alone.
- The source must match the machine head for head in the walk: a source that folds a guard the machine keeps fails
  with "the machine branches but the source ..." (checked by a control in the option 2 spike, below).
- `Src::Prim` holds Word operators only (`proof/gate.rs#parse` admits a `Shape::Prim` there only for a `Class::Word`
  row; Bit compares appear only as `If` conditions), so guarding every `Src::Prim` guards exactly the Word sites, as
  the machine's `Leaf(Class::Word)` constructor does; `Leaf(Class::Bit)` is a separate constructor and keeps its
  meaning.
- `mod`'s condition `not (eq_bv y 0)` is stuck on `y`; through the probe it is compared by `def_eq` and both branches
  are walked. `z` against `z` needs the `refl` rule.

Not picked:
- **Fold total guards and step at 1** ("option 2": a hypothesis `CH R 1 t e = t`, a walk rule, a source fold).
  Built (patch `docs/superpowers/spikes/2026-11-13-fold-and-step-at-1-spike.patch`, on the old step): correct, no
  cheaper then. On the linear step it would only remove the constant factor on total sites (expected, not measured).
  Parked: "Fold total-row guards", trigger: the gate's check time on Word-heavy programs matters.
- **An 8th constructor for partial rows** ("option 3"): the same constant-factor saving, for a constructor, an
  `Option<Dom>` and a case in each dispatcher; turned down 2026-11-13.
- **Keep the cache in `jit/shape.rs` and have eval call it** (spec review, 2026-11-13: drops the cache move and its
  caller churn): this is option (c) of the decision file's "Open: where the domain lives", an upward `lang -> jit`
  edge, turned down when (a) was picked; the reason still holds, since `lang` imports nothing outside `lang` today.

## Design

The spike patch closest to this design is `docs/superpowers/spikes/2026-11-13-word-row-guard-on-the-linear-step-spike.patch`
(against `5b062ee`); it has no `Dom` struct, no table cache and no eval change, and its guard-dropping control is a
thread-local this design does not keep (section 6).

### 1. `Dom` (`tatic-wasm/src/ops.rs`)

```rust
#[derive(Clone, Copy)]
pub struct Dom {
    /// The domain on words: eval's and the table test's definition.
    pub holds: fn(i64, i64) -> bool,
    /// The same predicate as a `V -> V -> Bv_1` circuit builder; every reader calls it through `constant_n`.
    pub circuit: fn(usize) -> Expr,
}
```

- `Dom::TOTAL = { holds: |_, _| true, circuit: dom_true }`, `dom_true(n) = \x:V. \y:V. 1` (the one-bit literal).
- `NONZERO_SECOND = { holds: |_, y| y != 0, circuit: nonzero_second }`, with `nonzero_second(n) = \x y C k. k (not
  (eq_bv y 0))`, the form of `eq_bit`, from `docs/superpowers/spikes/2026-11-10-partial-row-spike.patch`.
- `Row` gains `dom: Dom`. `circuit_row!` takes an optional domain argument, defaulting to `TOTAL`; `const_row`,
  `local_get_row` and `local_set_row` carry `TOTAL` and nothing reads it (my call: a field on every row, against a
  `Dom` inside `Class::Word`, which would turn every `.class ==` comparison and `matches!` on a class into a match).
- Bit rows carry `TOTAL` and their sites are not guarded (picked 2026-11-13, narrowing the earlier pick of "every
  Word/Bit row"). Every Bit row is total today; guarding Bit sites would add a guard to
  every `If` compare with no partial row to need it. The `binop` closure in `machine.rs#interp`, shared by Word and
  Bit, splits so only the Word path guards.
- `Row` derives `Clone, Copy` (its fields are a name, a class and function pointers), so the table test's negatives
  build a modified table as `Table::new` over rows copied through `names()` and `*row(name)` (`rows` is private; the spike's `twin()` copied field by field).

### 2. The table, cached in `tatic-wasm` (`tatic-wasm/src/wasm.rs`)

- `wasm::table() -> &'static Table` from a `static TABLE: OnceLock<Table>`, the one constructor (a test that wants a
  modified table copies its rows into `Table::new`; plan review, 2026-11-13, dropped a separate `build()`). church-bv's default test `job.rs#hidden_state_is_classified`
  scans `tatic-wasm/src` for such statics: the same commit adds `("../tatic-wasm/src/wasm.rs", "TABLE", "the wasm
  table: built once, pure")` to its `PROCESS_WIDE` array (declared length 9 to 10).
- `jit/shape.rs#wasm_table` is deleted; its callers (by the review's grep: 51 calls in 13 files, some by full path
  `crate::jit::shape::wasm_table()` with no `use` line, plus `shape.rs#is_comparison` and two comment mentions) call
  `tatic_wasm::wasm::table()`. Inside `tatic-wasm`, 17 `crate::wasm::table()` sites and one bare `table()` in
  `wasm.rs`'s test take the reference (most compile unchanged by deref). The plan recounts both with grep first.
- New row, placed after `mul`: `circuit_row!("mod", Class::Word, rem_s, "i64.rem_s", NONZERO_SECOND)`, named `mod`
  because `PrimOp::Mod.name()` is `mod`. `rem_s` is the spike's signed-remainder circuit (`encoding/gates.rs#rem_s_bits`,
  restoring division of the magnitudes; `wrapping_rem`, with `x % 0 = x` inside the circuit, never observed because
  the guard answers `z` there), with its literal tests, which include a negative dividend and `(i64::MIN, -1)` (wasm
  gives 0, no trap); `agree` also reaches both through `EDGES = [MIN, -1, 0, 1, MAX]`.
- `wasm_rows_are_closed_and_typed`: `mod` joins the `names()` list and the `cases` array (12 entries), and every
  row's `dom.circuit` must infer `V -> V -> Bv_1`.

### 3. Eval (`tatic/src/lang/eval.rs#apply_prim`)

- Before the operator match: `if let Some(r) = tatic_wasm::wasm::table().row(op.name()) { if !(r.dom.holds)(x, y)
  { return Err(EvalError::DivByZero) } }`. `Mod`'s hand-written zero check goes. `Div`'s stays (no row; see "Not in
  scope"), so "one definition" holds for `mod` alone until Div gets a row. The error keeps its name (my call). The
  by-name lookup (a scan of 11 rows) runs on every primitive application (building the table stores function
  pointers only; no circuit is built until a reader calls one); the plan times eval on a primitive-heavy term before and after, and indexes
  rows by `PrimOp` only if the lookup shows.

### 4. Lowering (`tatic/src/jit/lower_wat.rs#node`)

- The `PrimOp::Mod => raw(w, "i64.rem_s")` arm goes; `Mod` falls to the generic `row_of(op, Class::Word, ..)` arm.

### 5. The guard

- `z` reaches the builders: `MeaningEnv` and `SEnv` gain `z: At` (not an `Option`); `G::bm` and `G::bs`
  (`machine/statement.rs`) take it from `Ctxt.z`, which `bm_bs` holds. `z` is the statement's one out-of-fuel answer,
  bound once outside every entry; `At` is a level, so callee bodies, loop bodies and every fuel step read the same
  binder, and out of domain answers the very term out of fuel does. The spikes had `MeaningEnv.z: Option<At>`, `None`
  in the hand-built envs; the plain `At` is a deviation from what section 7 measured, covered by its `p1_probe`
  re-check. The two hand-built `MeaningEnv`s (`machine.rs`'s test near line 806,
  `machine/loop_tests.rs#meaning_env`) add an `R`-typed `z` binder and re-index their telescopes.
- `choose` stays as on main since `5b062ee`: the closed `machine.rs#choose_fn` applied to its four arguments, never
  unfolded. (The spikes' earlier "branches as arguments" form is superseded by it.)
- Machine: the `Leaf(Class::Word)` constructor's meaning is `self.choose(d x y, rest (op x y), z)` (the probe in the walk, the real
  `choose` in the statement); `ctor_ty` for Word grows by the domain's `V -> V -> Bv_1` argument, which the program
  builder passes per site as `constant_n(row.dom.circuit, n)`. `interp`'s `shape` helper takes a list of extra operands
  in place of one `Option`, and `seq_step`'s `cons` inserts the domain operand.
- Source: `cps`'s `Src::Prim` arm marks `y` as it marks `x` (it
  appears in both `dom x y` and `op x y`; unmarked, a right-nested `a % (b % c)` would copy it per level) and emits
  `e.choose(dom x y, k(op x y), z)` with `z` from `SEnv.z` (no wrapper: the arm is its only caller), reading `dom` from the row it reads `op` from. The copy of `cps` in
  `machine/sim/tests.rs` changes the same way. No guard is folded, total rows' included. `Src::Prim` is Word-only
  (Decided, facts), so no class test is needed on the source side.
- Walk: `Sim::sim_step` gains, last, `if def_eq(&mw, &sw) { return Ok(refl(..)) }`, for `z` against `z`. A guard
  inside an `If` operand wraps the whole `If` on both sides in the same order, and the `CH` rule's four-argument shape
  covers both, so nothing else changes (the spikes accepted `\a b. if a % b == 0 then a else b`).

### 6. Tests

- First task: the `mod` row, the guard and the `refl` rule, then gcd through the gate (the spikes accepted it; stop and
  report if the real build does not), and `agree` compiled against `wasmtime::Trap::IntegerDivisionByZero` (the
  variant's name is expected, not checked: wasmtime 42.0.1's source is not in the local registry).
- `op_table_tests.rs`: `agree` takes a `&Table`. Per pair, if `!(row.dom.holds)(x, y)`, wasmtime must trap with the
  integer-divide-by-zero trap and eval must return `Err(DivByZero)`, and the circuit is skipped; otherwise as today.
  Eval reads the same table, so its agreement with `holds` is by construction; wasmtime is the independent check of
  the domain. Every row's `dom.circuit` (the table's, not only the source operators') must equal `holds` on every
  pair (`def_eq` with the literal bit), checked after the per-operator loop. `EDGES` holds
  0, so the default test checks `mod` at b = 0. Two negatives, one per new check, run `agree` at the one pair (5, 0)
  on `table()`'s rows copied with `mod` changed: `mod`'s `holds` on the wrong operand (`x != 0`; wasmtime traps where
  `holds` says in-domain, and the wasmtime call runs before eval and the circuit checks, so it fails first without a matching
  test-built circuit), and `mod`'s `dom.circuit` set to `dom_true` with `holds` kept (the circuit and `holds` disagree
  at b = 0); `agree` must fail on each. `try_compile` and the lowering still read the global table,
  so a modified table changes only the circuit and domain checks, which is all these need. These are mistakes the
  gate accepts by design (both sides read the one table), so the table test is their only check.
- `every_prim_op_with_a_row_names_it`: only `Div` lacks a row.
- `proof/tests/gate.rs`: drop "gcd (Mod)" from `what_cps_cannot_take_is_not_covered`; keep "a / b" and "a / 0". New
  `gcd_is_accepted` gates both gcd samples, and `\a b. if a % b == 0 then a else b` (`%` inside an `If` condition's
  operand) must be `Accepted`.
- `machine/sim/tests.rs` (the walk's own tests, with their copy of `cps`): a `\a b. a % b` case, code
  `[get 0, get 1, row("mod")]`, joins the accepted list; two source-only mutants of it, built by calling
  `SEnv::choose` directly, must be `Rejected` at the walk: the guard's condition the literal 1 in place of `dom x y`
  ("the branch conditions differ" in the spikes), and its else `k(op x y)` in place of `z` (the guard vacuous; an
  else of type `V` such as `x` would be ill-typed, so the kernel, not the walk, would reject it). A mutant is a
  hand-written `SrcFn`, not a `Src`, and the `Machine` is built inside `run`'s checking thread, so `run` takes a
  builder from `&Machine` to a boxed `SrcFn` (the accepted cases wrap `cps`); the mutants mark `y`
  as the fixed `cps` does, and compute `k(c, op x y)` before calling `choose`. The spikes' other controls are not
  kept: a twin row `mod_total` (a table with a total `mod` named by an `Ins` edit) tests the same condition mismatch
  from the machine side at the cost of a second table and a gate entry taking one (spec review, round 2), and the
  guard dropped from the shared Word meaning needed a test-only thread-local in `machine.rs`, which church-bv's
  `hidden_state_is_classified` rejects.
- `z` pinned: the gate shows source equals machine, and both read `z` from the same binder, so a guard whose else is
  wrong the same way on both sides would pass it. In `machine/sim/tests.rs`, the source side for `\a b. a % b` is
  built directly, since `statement_with` returns a closed Pi type and no test reduces one today: under a telescope
  over `R, z, a, ks`, the real `Ctxt` (`Ctxt::new` at a fuel numeral, as `statement_with`'s unquantified branch
  builds it) gives the entry's source term, applied to `a`, the literal 0 and `ks`; its `whnf` must be `z`. The plan
  adds this as a small helper beside `statement_with` or in the test file. It checks the source side only; the
  machine equals it by the gate. Eval's error and wasmtime's trap at b = 0 are `agree`'s.
- Guards off the tail call: gcd's `%` sits in its tail self-call's argument. `\a b. if a % b == 0 then a else b`
  (above) covers an `If` operand; a non-recursive callee holding `%`, and a loop whose body uses `%` outside the tail
  call's arguments, must also be `Accepted`.
- `gate_mutants.rs#every_row_has_an_operator_swap_mutant`: `mod` gets a carrier (`gcd`, asserted to hold `mod` and to
  be `Accepted`). With `mod` after `mul`, `next` gives `mul -> mod` and `mod -> add`; both must be `Rejected` at the walk.
- `proof/tests/toy_table.rs`: `as_wasm` is a copy of the wasm row (`*row`, `Row` is `Copy`) and `toy()`'s `sub` literal takes `Dom::TOTAL`.
- `baseline.rs#VERDICTS`: both gcd rows `Accepted`, regenerated by `print_verdict_rows` and diffed.
- `loop_form.rs`: gcd's emitted loop proves (gcd is a tail self-call and takes the v0.9 loop form, which the
  2026-11-10 spike predates).
- Linear-work tests for `a % (b % (a % ..))` and `((a % b) % a) % ..` nested to depths 16, 32, 64, beside
  `gate_check_work_is_linear_in_an_if_chain` and in its style (check and build under 2.2x per doubling). The spike
  measured the right-nested chain's check only; its build and the left-nested chain are first measured by these
  tests.
- End of plan, once, through `run.ps1`: the ignored `tatic-wasm` and `tatic` proof suites, and church-bv's default
  tests (`hidden_state_is_classified`).

### 7. Cost

Measured on the closest spike (patch above, runs `2026-11-13-a1s3-*`; doc 15, "The gate's branch step made linear
(2026-11-13)"), check/build work against main plus the probe at `5b062ee`:

| program | main | this design |
|---|---|---|
| capturing_closure_loop | 8485/6409 | 9288/7275 |
| straight_line | 28603/3866 | 29241/4530 |
| held_out_b | 30481/6562 | 31449/7568 |
| doubling(6) | 9981/11617 | 26170/19762 |
| doubling(12) | 336627/570343 | 1346914/1074514 |
| gcd / gcd_with_two_base_cases | NotCovered | 61609/7037, 62100/7613 |

Every series is linear: the tree (check [47174, 89138, 173022] at doubling_7..9, 1.89x and 1.94x against the
existing test's 2.05x bound), the `if` chain (1.72x, 1.84x per
doubling) and the nested `%` chain (1.02x to 1.47x per doubling of depth, 4 to 256); the budget tests pass. The
plan's build is checked against these numbers once, with `p1_probe` (from the spike patch, kept as an ignored test or
dropped at the end); a figure well off them (say 20%) is investigated before the plan closes. The `MAX_GATE_TREE`
and `CALL_WEIGHT` budgets were fitted before any guard and are not refitted (they passed in the spike).

## End-state fit

| Change | Target | Replaces | Deletes |
|---|---|---|---|
| `Dom`, `dom_true`, `nonzero_second`, `circuit_row!`'s domain | `tatic-wasm/src/ops.rs`, `encoding/gates.rs` | nothing | nothing |
| `Row.dom`, `Row: Copy` | `tatic-wasm/src/machine.rs` | the spike's field-by-field row copies | nothing |
| table cache | `tatic-wasm/src/wasm.rs#table`, church-bv `job.rs#PROCESS_WIDE`; every `wasm_table` caller (tests included; the plan recounts) | `jit/shape.rs#wasm_table` | `wasm_table` |
| eval reads the domain | `tatic/src/lang/eval.rs#apply_prim` | `Mod`'s hand-written zero check | that check (`Div`'s stays) |
| `mod` row, `rem_s` | `wasm.rs`, `encoding/gates.rs` | lowering's raw `i64.rem_s` | the raw arm in `lower_wat.rs#node` |
| `z` in `MeaningEnv`/`SEnv` | `machine.rs`, `machine/statement.rs`, the two hand-built test envs | `MeaningEnv` without `z` | nothing |
| Word guard | `machine.rs#interp` (the `binop` split, `shape`'s operand list), `ctor_ty`, `seq_step`, the program builder's per-site `constant_n(row.dom.circuit, n)` | unguarded Word leaf | nothing |
| source guard | `proof/gate.rs#cps`, `machine/sim/tests.rs` | unguarded `Src::Prim` | nothing |
| `refl` on equal sides | `machine/sim.rs#Sim::sim_step` | nothing | nothing |
| tests | `op_table_tests.rs`, `proof/tests/gate.rs`, `machine/sim/tests.rs`, `gate_mutants.rs`, `toy_table.rs`, `baseline.rs#VERDICTS`, `loop_form.rs` | `what_cps_cannot_take_is_not_covered`'s gcd case | that case |
| docs | `docs/TOUR.md`, comments (list below), `PARKED.md`, `ROADMAP.md`, decision file, doc 15 | stale wording | "The partial row and gcd" in `PARKED.md` |

Docs, in full:
- `docs/TOUR.md`: the table's home, `Dom`, the partial row.
- Comments that name `shape::wasm_table` or say `mod` has no row, or describe the Word constructor without its
  domain: `proof/gate.rs` module doc, `jit/op_table_tests.rs` header and the "six non-`Div`/`Mod` operators" line,
  `jit/lower_wat.rs` near `emit_wrapping_div`, `jit/shape.rs` (the deleted function's doc), `lang/term.rs` near
  line 27, `wasm.rs`'s module doc ("the word rows `add` `sub` `mul`") and `wasm_rows_are_closed_and_typed`'s doc,
  `machine.rs`'s module doc (the `word` constructor's type) and the `Row`/`Class` docs. `cite_check` and
  `tour_check` do not catch comment drift; the plan greps for `wasm_table`, `rem_s`, "no row" and "Div/Mod".
- `PARKED.md`: delete "The partial row and gcd"; add "Div as a partial row", "Fold total-row guards" and "Guard Bit sites".
- `ROADMAP.md`; the decision file's "Open: where the domain lives" heading to decided; a doc 15 section with the
  build's numbers and its README line.

## Not in scope

- **Div**: its `MIN / -1` wrap needs the lowering's wrapping sequence modelled as instructions. It stays
  `NotCovered`, with its own zero check in eval. Parked: "Div as a partial row", trigger: a target that divides.
- Rows carrying each op's concrete semantics so `apply_prim`'s match goes (the decision file's later step on option
  (a)). Parked with the Div entry.
- Guarding Bit sites. Parked: "Guard Bit sites", trigger: the first partial Bit row.
- Folding total-row guards (the Decided section's option 2). Parked: "Fold total-row guards", trigger: the gate's
  check time on Word-heavy programs matters.

## Risks

- The gate accepts a domain or circuit that is wrong the same way on both sides; only the table test catches it (by
  decision). Out of domain and out of fuel both answer `z`, so trap and timeout are not told apart (by decision);
  the `z` pin shows the source side answers `z` out of domain; the gate carries it to the machine.
- Every Word site becomes a branch the walk steps over: check work on Word-heavy straight-line code rises by a
  constant factor (`doubling(12)` 4.0x), accepted 2026-11-13.
- The spike passed `proof::`, `tatic-wasm`, `jit::` and church-bv's default tests (but for its own thread-local), not
  the ignored suites; they run at the end of the plan.
