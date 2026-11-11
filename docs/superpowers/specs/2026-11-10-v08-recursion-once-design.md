---
status: draft
---

# v0.8: Recursion once (one generated simulation proof over an instruction table)

ROADMAP v0.8, Goal 1 (a JIT on proved equivalence). The shape was decided on 2026-11-10: z5, staged S0-S4, division by
zero a later partial row, the heap relation open (`docs/decisions/2026-11-10-v08-shape-and-any-backend.md`, "Decided
(v0.8 shape): z5, staged"). This spec fixes the stages and states the shapes for approval (D1-D5); it leaves no
choice open. Code facts are from `main` at `eba0891`; "inference" marks what no run showed.

**Cites.** Spikes are cited by heading of doc 15, the JIT and the target machine (index `docs/tier-cycle/README.md`);
patches are in `docs/superpowers/spikes/`, runs in `docs/runs.md`. **Census numbers** index the census list of
`docs/tier-cycle/`, "v0.7's first steps: the census and the emit spike": the 23 entries of `support/samples.rs#corpus`
(1-23), then the 15 builders of `testing/test_corpus.rs` (24-38). So 1, 2, 3 are factorial, `redundant_arithmetic_recursion` and fib; 13 is
`twice_inc_5`; 23 is `tail_recursive_loop_with_pap_producing_root_self_call_arg`; 34 is `let_bound_factorial_10`.

## Intent and why

v0.7 gates the straight-line fragment on a kernel proof of the emitted instruction list (`proof/gate.rs#gate`). Every
recursive or calling term still installs on a theorem about a model of the compiler (`jit.rs#kernel_verify`), not
about the code that runs. v0.8 moves loops, self-calls and direct calls to proofs of the emitted code, through one
simulation statement and one proof generator, over a machine whose instructions are rows of one table. The table is
also the seam for "any backend" (decision file, "Any backend: provided or explored, one trust story").

The spikes say this carries real terms:

- The generator proves both sum loops, factorial, `redundant_arithmetic_recursion` and fib from tatic's terms
  (`Source::cps`) against the lowering's code, with no per-function case (`docs/tier-cycle/`, "The generator on
  tatic's terms and the lowering's code: a spike").
- Tail self-calls lowered as `return_call` need no `loop` or `br`, and the walk did not change, though `return_call` had
  its own meaning there (the activation's return continuation; `docs/tier-cycle/`,
  "Tail self-calls as `return_call`, with no `loop` or `br`: a spike").
- One call constructor for every arity, with callee laws as hypotheses, carries 13, 23 and 34 (`docs/tier-cycle/`,
  "Modules, one call constructor and an `i32` kind: a spike"; its real-term verdicts are printed, not asserted).

## Goals

From the decision file's z5 "Done when" and ROADMAP's v0.8 line, refined:

1. Both sum loops (`capturing_closure_loop`, `partial_application_loop`) and census 1, 2, 3 install from emitted code
   through the generator, in their specialised form (the term and code `jit.rs#try_install` proves via
   `compile_specialised`), each within `MAX_GATE_TREE`. The gate's verdict is final for them. All five are mandatory
   and all five are single-entry modules (the entry is the only callee; their specialised goldens at `eba0891` hold one
   `func`), because S2c takes no other module. S2b's checkpoint stops if any is excluded or has a second entry, and
   the `Call` weight (Budget) is set so they stay under the budget, never over.
2. Direct calls 13 and 34, and term 23, install the same way, in specialised form. A target whose specialised code
   still has a heap, table or `local.set` line (S2b's no-`Raw` test) is `NotCovered` because `cps` answers `None` for it (D4),
   stays on `kernel_verify` and gets a `PARKED.md` entry; it does not shrink silently.
3. Two functions written without sight of the generator prove against it once frozen (S2c, "Held-out terms").
4. A mutant per row and per call site is rejected, each test naming the layer that rejects it (stack check, the
   walk's `Rejected`, or the kernel). A kernel negative (a proof checked against another statement) exists for a
   self-call term and for a call term, both at the `tatic` level. The statement is tested too: a statement mutant (a
   relation that ignores the continuation, one that drops the fuel quantification) makes the generator's proof of a
   self-call term fail in the kernel.
5. The five v0.7 fragment terms still install and the v0.7 mutations are still rejected; every term of the baseline
   fixture (below) installs, or fails to, as it did at `eba0891`; so does every term of the `Raw`-bearing class (the
   unspecialised forms of 13, 23, 34, `twice` and `partial_application_loop`, and the closure-record terms), by a test
   over that class, so `cps`'s predicate regresses none. The cap keeps its floor: `doubling(12)` still installs
   through the one statement within S2c's go/no-go time (Budget).
6. Deleted: the loop law, fuel 1, `strip_loop`, `gate_with`, `countdown`, `Dup`, and what D1 and D4 remove with them.
7. A toy second instruction table passes a straight-line term through the unchanged gate (S4; "installs" in ROADMAP
   read as the gate's verdict, since the toy has no runtime; inference from the wording, the user confirms).

**The baseline fixture** is a literal table, committed as a test first in S0 and passing at `eba0891` (S0 done-when),
with one row per census term; the held-out commit (S2c) appends a row per held-out term, its outcome measured by
running the fixture's harness in a worktree at `eba0891`. Goal 5's census comparisons read the S0 rows, its held-out
comparisons the appended rows. A row records whether the term installs, `stats.compiled`, `stats.specialised` and the
specialised term's tree size (`compile.rs#tree_size` of the source term, which no lowering change moves, so after S2b
only install outcome and counts are compared). S2b adds a membership column (the Goal 1 and 2 targets that pass its
no-`Raw` test, the node-count cap (the `Call` weight is not fitted until S2c) and a single-entry test, each with the stage that delivers it). It has no route column, so nothing reads
`in_fragment`, which S2c deletes. Goals 1, 2 and 5 compare against it.

## Non-goals

- gcd and the partial row: the decision file makes them the next rung (Parked).
- Terms 25 and 28: they need bit rows (`wrap`, `extend`, `shl`, `or`).
- Division and modulo: the wasm table has no `Div` or `Mod` row, so `Source::cps` answers `None` for a term holding
  one anywhere and the term is `NotCovered`; zero divisors stay with `kernel_verify` and `verify()`'s agreement.
- Closure records, the table and `call_indirect`, term 27, anything that allocates: they need the heap relation
  (Parked). Terms 13, 23 and 34 are in scope only specialised; their unspecialised goldens hold `call_indirect` or
  `$alloc` (`tests/golden/`).
- `(hp, heap)` in the state and `local.set` with the scratch locals `$envtmp`, `$papenv`, `$diva`, `$divb` (D2): no
  v0.8 target consumes them.
- Deleting or rewriting `kernel_verify`'s model provers: they serve every term outside the grown fragment; only their
  header claims change (S2b).

## Anti-goals

- A proof written for one loop or one function: the generator has no per-function case and no match on the
  instruction list (`docs/tier-cycle/`, "One generator for loops and calls, with locals apart from the heap: a
  spike"); it walks the two sides' kernel terms in lockstep.
- A gate branch per program shape: one law per instruction kind and one statement for every program, straight-line
  code included (D4).
- Per-row special cases in the schema: a row is data of one shape (D5).

## Constraints

- **The kernel does not change.** Conversion has no eta and there is no cumulativity (`docs/tier-cycle/`, "A store at
  a run-time address across a call, the cost of `call`, and eta: three follow-ups"), so the generator passes
  continuations in the machine's own form and states lemma motives at the sort they land in.
- **Trust.** Trusted: the rows, the printer, `Source::cps`, `Call`'s meaning, and the statement builder (the machine
  side's module fixpoint, the fuel quantification, the continuation relation), which lives in its own module apart from
  the untrusted walk (End-state fit). The walk is untrusted and the kernel checks every proof against the statement; it
  cannot notice a vacuous or too-weak statement, so Goal 4 tests the statement with mutants. A row's meaning is checked
  against eval and wasmtime by `jit/op_table_tests.rs`, never by the gate. Both sides read one row, and the right side
  is built from the source term, never the code (v0.7 spec,
  `docs/superpowers/specs/2026-11-08-v07-straight-line-gate-design.md`, sections 4 and 6). **Tail position** is derived
  from the code list: a call whose continuation is empty (nothing follows it in its function body, and every enclosing
  `If` is last) prints as `return_call`. `Call` has no tail flag and its meaning has no tail branch: with an empty rest
  its continuation is the activation's own, and `call` then `end` equals `return_call` in wasm, so the gate's proof
  covers the printed text. What stays trusted is the printer computing "empty continuation" correctly. "Followed only by `else` or `end`" is
  necessary, not sufficient: a call at the end of an `If` arm is followed by `else` or `end` even when the `If` has
  code after it (an operand-position `If`, `1 + (if c then f(x) else 0)`), and `return_call` there is wrong. So the
  printer check is a property test over generated lists, including an `If` with trailing code and a call at the end
  of an arm, asserting such a call prints as `call` and only a call with an empty continuation prints as
  `return_call`; the deep tail-loop test checks stack safety. A misplaced `return_call` cannot be stated as an `Ins`
  list, so it is not a mutant, and the gate cannot see it (`Call` has no flag). For a `NotCovered` term, which the
  printer change also reaches, the only guards are that property test, the differential compile fuzz and `verify()`'s
  samples.
- **Machine inputs.** `meaning` takes the module (D3; it indexes the callees) and the opaque `choose` probe `ch`. The
  activation's return continuation is the fold's own continuation argument, so it needs no hook.
- **Budget.** `proof/gate.rs#MAX_GATE_TREE` (8192 nodes; `doubling(12)` took 0.35-0.38 s, its doc comment) bounds
  cost for the straight-line fragment only: a recursive term costs far more per node (factorial, about a dozen nodes,
  took 7.6 + 68 ms at n = 64, against about 0.05 ms per straight-line node). One budget covers both: a term's cost is its tree nodes plus a weight per `Call` site, and a term over
  `MAX_GATE_TREE` is `NotCovered`. A straight-line term has no `Call`, so its cost is its node count and the cap is
  unchanged for it; S2's scaling probe fits the weight, recorded in the findings. The weight is a cost knob, not a
  goal: it is set so every Goal 1 target is under the budget (S2c). A Goal 2 target or held-out term over the budget
  leaves its goal. The cap may be raised on purpose, never lowered below `doubling(12)` (Goal 5). Every Goal 1 and 2 target is timed through `run.ps1`; the one go/no-go on time
  is S2's.
- **Deep builders** run under `tatic_kernel::grow`; checking threads use `tatic_kernel::CHECK_STACK`
  (`tatic-kernel/src/stack.rs`).
- **House guards** (repo `CLAUDE.md`) pass at every commit: size (1000 lines per `.rs`), test placement, tour
  (`docs/TOUR.md` moves with each module change), cite, layout, front matter, script header, stack literal, and doc
  index (2000 lines per doc; doc 15 has 1852, so v0.8's findings go in a new numbered tier-cycle file).
- **Long runs** (scaling tests, golden sweep, icount, timings) launch through `run.ps1`, timings with `-Timed`.

## Shapes for approval

These are architecture, so they need the user's approval, but the spec leaves each one shape: the other options are
ruled out by the anti-goals or by a spike, and stay as one-line rejections.

### D1 No `loop`: tail self-calls as `return_call`

Searched: tried removing `loop`/`br` outright, since the lowering's only `loop` wraps a function for its tail
self-calls (`jit/lower_wat.rs`, the tail `SelfCall` arm) and the generator treats `br` and `call` as one fuel edge.
Removed with them: `Dup` (its only user is `countdown`), the `$t` staging, fuel 1, the loop law, `strip_loop`.

- **The shape.** The lowering emits env words, arguments, then a call; the printer writes a call in tail position as
  `return_call` (tail-ness is derived from the list, Constraints). The machine has no `Loop` or `Br` and `meaning`/
  `interp` take no fuel; the fuel quantification (`GoodNat`) and the module fixpoint belong to the statement builder
  and the generator (D3, End-state fit), as the spikes built them in `sim.rs`.
- **Evidence.** Every target of the no-loop spike proved through the unchanged walk at n = 4, 24 and 64; a 10^6-
  iteration tail loop returns `n(n+1)/2` while the same WAT with `call` traps; wasmtime 42.0.1 accepts `return_call`
  under its default configuration, and every engine on main is `Engine::default()` (`docs/tier-cycle/`, "Tail
  self-calls as `return_call`, with no `loop` or `br`: a spike").
- **Cost.** At least 29 of the 34 goldens change once (S2b); a future source loop that is not a self-call must be lowered as
  one; run-time speed of the tail loops is unmeasured until S2b's bench run.
- Rejected: keeping `loop` (D1b). It needs a restart hook main does not have, two edge kinds that must agree and
  `LocalSet` with temporaries, or a loop law per shape, which the anti-goal rules out (`docs/tier-cycle/`, "The sum
  loop proved against a source recursion: a spike").

### D2 No mutable state: an immutable frame, no heap

Searched: under D1, tried removing `LocalSet`, the temporaries and the `$p`/`$t` printer split (all three go: today's
body `local.set` lines are the tail staging D1 deletes plus closure and division scratch no target reaches,
`jit/lower_wat.rs`); then locals from the state (nothing writes a parameter, and a callee's frame is a separate value,
so there is nothing to restore on return); then the heap (under a frame, nothing the gate emits reads or writes it; its
only consumers are the machine's store/load check in `wasm/laws.rs` and the abstract `mu` every gate statement
quantifies, `gate.rs#statement`). Removed with them: the `Store`/`Load` classes, `mu`, `Call`'s heap sort (j4's
explicit sort operand names it; what the operand becomes is D3's hypothesis), the printer's panic arms (every row has a printer line).

- **The shape.** The meaning takes a frame (nested pairs of slot values) and a stack, and no state. `local.get i` is a
  leaf row whose operand is a frame slot built at the literal index, failing at or past the slot count; a call builds
  the callee's frame with `unpack`.
- **Cost.** Untried: the spikes used the update-chain locals and the abstract memory, and the frame's type depends on
  the slot kinds, so a constructor or `Call`'s operand may need it; S2c step 1 finds out.
- **Fallback, taken in S2c step 1 if the frame does not type** (before the freeze, so nothing frozen reopens): the
  Parked update chain over a zero base, with no `LocalSet` and no restore. Only two things change: `local.get`'s
  builder is a chain lookup and `Call`'s `unpack` builds the chain; the heap, `Store`/`Load` and `mu` still go, and the
  statement, the generator, S3 and S4 are untouched. The commit records why, and the Parked line is edited to say it
  is in use. The store/load check and `wasm_scaling`'s store/load workload go after S0.
- Rejected: locals as an update chain over a zero base with a restore on return, and the abstract memory kept
  (`Store`/`Load`, `mu`): each carries concepts no v0.8 instruction or target consumes. Both return when a target
  needs them (Parked: "`LocalSet` and scratch locals", "The heap relation"). Rejected: `LocalSet` and the `$p`/`$t`
  naming now (the decision file's S1).

### D3 One `Call` over a callee index

Searched: tried removing the per-arity constructors and `MAXA` (removed: j4 fitted one constructor for every arity
to the kernel's levels, with the state sort as an explicit operand; dropping the operand is a hypothesis, below); the `ReturnCall` variant and a tail flag on `Call` (removed: `return_call` is `call` with an empty continuation,
so tail-ness is derived from the list and `Call` has no flag or tail branch; the printer computes it, Constraints);
`Ins::Call`'s argument count (removed: arity is
the callee's); the callee pairing search (replaced, not shown unnecessary: the `Call` term carries its index and the walk selects
the law by it, below; new in S3, j4's encounter-order pairing being the only evidence); the `i32` kind and kinds
operand (removed on a hypothesis, tested in S3); a self-call-only constructor before S3's (removed: built once).

- **The shape.** One structural class `Call`, kernel constructor `[A, unpack, idx, rest]`, with `unpack` building the
  callee's frame (its arity parameters, then its env words; the env word is slot `arity`). A self-call's index is the
  entry's own and its callee law is the induction hypothesis; in S3 another callee's law enters as a hypothesis that
  the callee's own closed proof discharges. At `Call(j)` the walk takes module entry `j`'s law (selected by the `idx`
  in the term; unspiked, see below), and the source continuation from `cps` must convert with it, so a wrong index
  fails in the kernel (or the stack check on arity).
  The meaning of `Call` continues with the meaning of `rest`, which for an empty `rest` is the fold's own continuation
  (the activation's return continuation).
- **How `meaning` gets its inputs.** `meaning` takes the module and `ch`, an opaque `choose` the generator proves
  against and then applies to the real one (the statement uses the real `choose`, `None`). There is no separate callee
  environment: callee laws are indexed by position, so `Call(j)` reads module entry `j` for its slot count and refers
  to the `j`th law the statement builder or the generator binds (a fixpoint component in the statement, a hypothesis in
  the generator). The walk is the spiked lockstep walk of the two sides' kernel terms; it matches on term shape,
  not on instruction tags, and selecting the law by the `idx` in the machine's term is new in S3 (S3's stop
  condition). `Source::cps` takes the same `ch`. The module fixpoint over fuel (`fuel H tm bm`) is not in `meaning`: the
  statement builder in `machine/statement.rs` builds it, with the fuel quantification and the continuation relation,
  and the generator in `machine/sim.rs` proves against it.
- **Evidence.** j4 proved 13, 34 and 23 and every earlier target with one constructor per call kind, always with the
  state sort as an explicit operand ("needed for the levels"), so the operand-free `[A, unpack, idx, rest]` is a
  hypothesis, not a result; and rejected a wrong callee, swapped arguments and a false callee law (`docs/tier-cycle/`,
  "Modules, one call constructor and an `i32` kind: a spike"). j4 paired callees by encounter order, unverified; it
  did not test the env word's kind (its argument swap never touched the env word). The evidence that `Call` alone
  proves tail self-calls is one accepted mutant (`call` for a tail `return_call`) in a machine that had the other
  constructor (inference for a machine without it; S2c proves every target with `Call` alone).
- **Fallbacks, decided in the stage.** The operand-free type is tried in S2c step 1, beside the frame (before the
  freeze). If it does not type, the explicit sort operand stays (j4's form; under D2 it names the frame or stack
  sort, since no state sort remains) and a Parked line records why. If S3's env-word swap is not rejected, the env
  word becomes a `K::I` kind (j4's form): that reopens frozen rows, so the builder stops and reports. If selecting
  the law by `idx` from the kernel term fails, there is no fallback: the builder stops and reports.
- Rejected: one constructor per arity up to a cap (`MAXA = 3`, the no-loop spike's form): capped arity, a constructor
  count that grows with the cap, rows repeated per arity.

### D4 One relational statement, one verdict

Searched: tried removing `gate.rs#statement` (refl, fuel 1, a frame in memory) as a second statement, and removed it.
Also removed an earlier draft's "convertible-first" rule (try `def_eq`, else apply the relation): it is out. Removed
`in_fragment` as a second acceptance rule kept in step with `cps`.

- **Why one statement.** The need is `Call`: after a call the machine runs the rest on the machine and the source on the
  source, equal only by the induction hypothesis (`docs/tier-cycle/`, "Calls by index proved against a source
  recursion: a spike"). The spike's remark that the types force a relation (the machine continuation took a heap, the
  source one did not) does not hold under D2, where straight-line sides could convert; so one statement for
  straight-line code is the anti-goal's choice (no route by program shape), not a necessity.
- **The statement.** Every covered term is the generator's simulation: fuel `N` with `GoodNat` and a continuation
  relation hypothesis; the proof applies the relation at the answer, with no convertibility try. A straight-line term
  is that relation applied once.
- **The verdict.** `gate` returns three answers. `NotCovered` is decided from the source alone: `cps` answers `None`,
  or the term is over the one budget (Budget); it goes to `kernel_verify`. There is no separate coverage predicate:
  `cps` translates only the heads and arguments the code can follow (no captured variable, no lambda that is not
  applied, only a literal or `Rec` head), so every shape whose lowering emits a `Raw` or heap line is a `None` by
  construction and a covered term never fails S2b's no-`Raw` test; a shape `cps` cannot refuse that way stops the
  builder (Goal 5's class test). For a covered term the gate is final: `Accepted`
  when the walk builds a proof and the kernel accepts it, `Rejected` when the code is ill-formed, holds a line the walk
  cannot take (`Raw`, an unknown row), the walk fails, or the kernel refuses. A closed term is the empty parameter fold,
  not a case.
- **Cost.** The straight-line gate's time through the induction wrapper and transport is unmeasured; S2's go/no-go
  decides it. A recursive term costs far more per node than straight-line code, so tree size alone does not bound it;
  S2's scaling probe fits the per-`Call` weight in the one budget (Budget). A walk gap on correct code of a covered term loses an install `kernel_verify` gives today; the baseline
  fixture is what catches it.
- Rejected: the refl path kept for straight-line code (D4b): two statements and a route by program shape, against the
  anti-goal. It is not a fallback either: S2's go/no-go is about the cap alone, and a no-go amends Goal 5's cap (the
  user's call), never keeps two statements. Rejected: falling back to `kernel_verify` after `Rejected`: the walk cannot
  tell a wrong body from its own gap, so a wrong body would install whenever the model theorem holds (v0.7's contract,
  `jit/tests.rs#the_gates_verdict_is_final_for_fragment_terms`).

### D5 Rows as data, the table a value

Searched: tried removing a `Backend` trait (removed: the table is a value), the spike's `ops::CTRL` global (removed: a
control is a mutated table), the constructor-count literal (derived: the count is the number of classes), a second list
of structural constructors (they are classes with no rows), the row handle and `shape::op_of` (`Ins` holds the row's
name), the constructor type as a row field (derived from the class), a separate source-operator map with its generic
parameter (a row's name is the key), and the row's stack-effect field and operator-function operand (the class fixes
the first; the row's name selects the second). Searched again with those gone: one 2-to-1 class with a result-kind field on the row, which fails because the
constructor type reads the kind and a field would be a second source for it; nothing else.

- **A `Row`** is a plain record: name, meaning builder, printer line. The leaf class fixes the stack effect and the
  result kind, so a row cannot disagree with its constructor. Three classes, the leaf arms of `wasm.rs#ctor_ty` today:
  0 to 1 (one numeral operand; `push` and `local.get` are two rows, whose builders are `lit n` and the frame
  projection at `n`, failing at or past the slot count), word-valued 2 to 1 (`V -> V -> V`, one row per arithmetic
  `PrimOp`, no operand) and bit-valued 2 to 1 (`V -> V -> Bv_1`, one row per comparison). The two 2-to-1 classes differ
  only in result kind, and the class is where that lives: `Op::kind()`, `shape`'s stack effects, `If`'s bit pop,
  `gate.rs#operand` and `shape::is_comparison` (also called by `ir.rs`, `compile.rs` and `proof/universal.rs`) all
  become a lookup of the row's class ("is bit-valued"). A later unary row (`wrap`, `extend`) adds a class, not a field.
  The constructor type is derived from the class: every leaf arm has the shape `operand -> rest at the output stack ->
  result at the input stack`. `Store` and `Load` are not rows: they stay structural classes (below) until S2c deletes
  them.
- **A `Table`** is one ordered list of constructor classes: a leaf class owns named rows; a structural class (`If`,
  `Call`) has a hand-written type and meaning, no rows, and a tag the walk looks it up by, never by position. Code with
  an instruction whose tag the table lacks is `Rejected`.
- **The source pairing is a name.** `PrimOp::name()` (new, in `lang`) is the key; `Source::cps` and the lowering find
  the row by it, and a name with no row is a `None` from `cps`. `tatic-wasm` knows no `PrimOp`, so there is no
  dependency cycle. The table test checks each named row against eval and wasmtime, as it checks `op_of` today.
- **Placement** (End-state fit): backend-independent code (the gate) takes the table as a value; the wasm front end
  and lowering name the one wasm table through one accessor in `jit/shape.rs`.
- **Cost.** `Ins` loses its named leaf variants for `Ins::Row { name, operand }` (operand only for the 0-to-1 class), keeping `Store` and `Load` as variants of their structural classes until S2c;
  dispatch is a lookup (S0 measures).
- Rejected: an enum with derived parts (D5b): a second table is a second enum, so the gate needs the trait the decision
  file removed. Rejected: `Table<S>` generic over a source key, or `PrimOp` moved into `tatic-wasm` (reverses layering).

## Departures from the decision file

For approval with the shapes above: its S1 (locals as a state component, `local.set` a row) is dropped under D1 and
D2; its S0 check by equality of derived and old constructor types, meanings and printed WAT becomes the existing tests
pinning both (kernel checks pin types and meanings, the goldens pin printed lines); its "Done when" has 13 and 34
installing, here conditional on S2b's no-`Raw` test (Goal 2).

## Stages

Every commit ends green. There is no S1 (dropped, above). The fork rule: a fallback named below is taken in the stage
and recorded in the commit and, where it leaves a gap, in `PARKED.md`; a fallback that reopens frozen code, or a stop
condition, stops the builder for the user. So does a Goal 3 failure (S2c): S3 and S4 wait for the user, who chooses
between amending the generator with a new held-out pair (the freeze reopens once) and dropping the no-per-function-case
claim as a recorded finding.

### S0 The instruction table over today's constructors

- **Builds.** The leaf instructions (push, the word-valued and bit-valued binary ops; `local.get` stays today's
  `push; load` until S2c, where it becomes a second 0-to-1 row) become rows. `Store` and `Load` stay structural
  classes with today's hand-written types, meanings and printer lines, though D2 deletes them in S2c: `local.get` is
  `push; load` and the tail loop's staging writes `$p` until S2b and the frame step, and a temporary row class for
  them would be built only to be deleted. The rows have one schema in `tatic-wasm/src/machine.rs` (D5). The table derives what `wasm.rs` writes by hand today:
  `ctor_ty`'s leaf arms, `interp`'s leaf vector, `seq_step`'s constructor indices, `shape`'s stack-effect tables (now
  the leaf class's effect) and the constructor count. `If`, `Loop`, `Br`, `Store` and `Load` are structural classes (the loop pair until S2b, the memory pair until S2c). `gate`, `statement` and `Source::cps`
  take `&Table` from here on, which is what makes S4's "no diff in the gate" reachable. `Ins` leaf variants become
  `Ins::Row { name, operand }`, and `PrimOp::name()` replaces `shape::op_of`.
- **First, the baseline fixture** (Goals, "The baseline fixture"), census terms only, committed alone at `eba0891`
  behaviour, without the membership column. **Then, a mechanical deletion:** `countdown`, `countdown_law` and `Dup` (D1). The test
  `countdown_invariant_is_not_exponential` is also the only regression guard for `conv`'s pair memo (its doc comment;
  `tatic-kernel/src/reduce.rs` cites the doc 15 finding, not a test), so it moves first to a kernel test on a small
  shared-tail case tree.
- **Done when:** the fixture passes at `eba0891` before any other S0 change; every existing test passes and the 34
  goldens are byte-identical; the new memo guard is red with the
  memo lookup disabled (a recorded run, its diff kept as a patch) and green with it on, within a stated time bound, or,
  if no small case exists, a `PARKED.md` entry says the guard goes and why; row dispatch costs within noise by
  instruction count (median within 0.5% of the post-deletion baseline, or the A/A spread if larger; ICOUNT.md, rotated
  arms, max/best read for large-page wander) on `wasm_scaling` and the gate's two linear-work guards.
- **Deletes:** the hand-written `ctor_ty` leaf arms, the `interp` literal, the count literal, `seq_step`'s per-op
  indices, the `Ins` leaf variants, `shape::op_of`, `countdown`, `countdown_law`, `Dup`, the old memo test.

### S2 The generator on `Source::cps` with self-calls

Two parts: S2b changes the lowering and needs no generator; S2c builds the generator and the one statement.

#### S2b Every call emitted, no `loop` (D1)

- **Builds.** The lowering emits every self-call and known-callee call as `Ins::Call(callee)` after its env words (the
  tail self-call gains env forwarding, absent today), with no wrapper, staging or `br`. The env-word lines
  (`i32.const N`, `local.get $env`, `local.get $e{k}`) become rows; closure-record lines stay `Raw`. `CompiledFragment`
  carries a module: an ordered list of entries (name, `slots` = the words a call pops, arity plus env words, code, and
  from S3 the source term), indexed by the callee index `Call(j)` carries. S2b assembles an entry for every callee the
  lowering emits, in registration order (`PendingCombinator::Literal`), which is the index mapping, so the printer
  prints `call $c{f}` from it; the printer and `well_formed` read it, and
  `gate` takes it from S2c on. `Ins::Call` carries no tail flag and the
  lowering threads no tail position: the printer writes `return_call` for every call, self or known, whose continuation
  is empty (Constraints), so the IR and `lower_wat.rs`'s `node()` do not change for it. Until S2c gives `Call` a meaning the gate takes no calling term, so every one stays on
  `kernel_verify` (a stopgap closed within S2). The model
  provers state the IR's tail self-call as `loop`/`br`; they should pass unchanged, and their headers now say the loop
  stands for a `return_call`.
- **Then the loop machinery goes**, in its own commit once nothing emits it: `Ins::Loop`, `Ins::Br`, the loop stack,
  the printer arms, `loop_law`, `timeout`, `Wasm::good`, `gate_with`, `strip_loop`, fuel 1 and the `fuel` parameter of
  `meaning`/`interp` (fuel served only the loop). The refl `statement` stays, without fuel, as the acceptance path for
  straight-line terms until S2c step 2 replaces it.
- **Done when:** the suite passes with exactly the goldens that hold a `loop` or a call in tail position regenerated
  (the plan counts them: 29 hold a `loop`; a tail known-callee call now prints `return_call` too, so the count may
  grow) and the 5 `rejects_*` goldens byte-identical; the differential compile fuzz passes; a deep tail loop test installs a tail sum loop, runs n = 10^6
  through `jit.apply` with `stats.compiled` 1, and its hand-written `call` control traps; `kernel_verify`'s provers pass
  with only header edits; the no-`Raw` test over the specialised code of every Goal 1 and 2 target writes the
  fixture's membership column (the Goal 1 and 2 targets: both sum loops, 1, 2, 3, 13, 23, 34; its cap test is node
  count only, the `Call` weight being fitted in S2c; its single-entry test must pass for every Goal 1 target; the
  held-out terms carry their own no-`Raw` assertion); one recorded `-Timed` before/after bench of `gcd_tail_recursion_to_loop` and
  `capturing_closure_loop` (`benches/execution.rs`) is in the findings file (a slowdown is a finding, not a gate).
- **Checkpoint.** If the membership column excludes any Goal 1 target (either sum loop, census 1, 2 or 3; a second
  module entry excludes), or all of
  13, 34 and 23, stop and report: S2c-S4 would prove less than the goals. Goal 2 targets excluded one by one are parked.
- **Deletes:** the loop machinery above, the `(local $t{i})` declarations and the tail staging.

#### S2c The frame, the one statement, the `Call` meaning and the verdict

- **Builds, in order:** (1) the frame (D2; if it does not type, D2's fallback), after which nothing emitted reads
  the heap, so `Store`, `Load`, `mu` and the store/load check go here; (2) the one statement (D4) in
  `machine/statement.rs` on straight-line terms, replacing the refl path, on a worktree branch merged only on a go;
  (3) `Call`'s meaning over the module (D3), the generator in `machine/sim.rs`, the walk and `cps`'s self-call case
  (with the `choose` hook) (`cps` returns `Option`, strips an optional `Rec` then
  `arity` `Abs`, and keeps "an `If` only in tail position"), with `in_fragment` replaced by the three-way verdict, `cps`
  refusing `Raw`-bearing shapes (D4) and the module with its entries (S2b), where a module with a callee other than
  the entry is `NotCovered` until S3 gives the callees source terms; (4) leftover deletions and docs: the freeze.
- **The go/no-go (S2's).** The median of 5 `run.ps1 -Timed` runs of the relational `doubling(12)` build and check is at
  most 0.57 s, 1.5 times the refl curve's 0.38 s re-measured in the same session. The test is about the cap (the
  targets' trees are a few dozen nodes), which cannot drop below `doubling(12)` (Goal 5). A second probe fits the `Call`
  weight (Budget): a generated family of self-recursive terms with 1, 2, 4, ... call sites and branches, timed through
  `run.ps1 -Timed`; the weight is the one that puts build plus check at the JIT path's 0.4 s at the budget. It is a
  cost knob, not a goal: once it is fitted, the budget is checked again for every Goal 1 and 2 target (nodes plus
  weight, which S2b's node-count test could not see); if the weight puts a Goal 1 target over, lower it and record why
  in the findings, and if a Goal 1 target alone exceeds the time the JIT path allows, stop and report; a Goal 2 target
  over leaves its goal (Budget). A no-go on the cap does not keep the refl path: it stops and returns to the user, who amends Goal 5's cap floor;
  the end state has one statement. The linear-work guards keep their 2.05 bound.
- **Held-out terms.** Before step 1, a subagent given only the shape this spec says `cps` takes writes two terms
  outside the goals (say, a two-parameter non-tail recursion and a tail loop of another step shape), committed as
  ignored tests asserting `Accepted`, within the budget and with no `Raw`, together with their fixture rows
  (Goals, "The baseline fixture"). The freeze is every non-test file under
  `crates/` at step 4 and ends when S3 starts; un-ignoring touches only test paths, and a failure is Goal 3 failed,
  which stops the builder for the user (fork rule). The held-out terms join Goal 5's regression set: S3's done-when re-runs them, and a failure there is an S3
  regression, not an unfreeze.
- **Done when:** Goal 1, Goal 5 and S2c's Goal 4 set hold with asserting tests (the spikes' `gen_real` tests printed
  failures instead); the fixture's verdict column is filled; the targets are timed in one recorded run; Goal 3 holds
  after the freeze. S2c's Goal 4 set: v0.7's `gate_rejects_mutations` carried to the one statement over the five
  fragment terms plus factorial; one operator-swap mutant per `Op` row; per self-call site the argument index, order, a
  dropped or extra argument and a dropped call; the no-loop spike's list (`docs/tier-cycle/`, "Tail self-calls as
  `return_call`, with no `loop` or `br`: a spike"), minus its `return_call`-for-`call` mutant, which no `Ins` list can
  state; factorial's proof against fib's statement; the statement mutants of Goal 4. Each test names the layer observed.
- **Edge cases, one test each:** a covered term's code with a `Raw` line, or ill-formed, is `Rejected` and not
  installed; the cases `cps` cannot take (`twice`, `\f. f 1`, an `If` in an operand or condition, `a / b`) are
  `NotCovered`; gcd (`Mod`) and a `Div` by a literal zero are `NotCovered` and install as in the fixture; a closed
  straight-line term takes the gate route.
- **Deletes:** the refl path, `in_fragment` (and its `arity == 0` clause and `unreachable!` arms), the frame-in-heap
  encoding, `LocalGet`'s `push; load` expansion. **Guard:** none added: the deleted items are code symbols, so the
  compiler fails on any use, and the docs grep covers prose; the closing report says so.

### S3 Modules: calls that name their callee

- **Builds.** Each module entry (S2b) gains its source term, which comes from the lowering's registration of the callee
  by its source lambda's hash (`jit/compile.rs`, `PendingCombinator::Literal`); the gate's signature does not change; a `PartialApp` callee has no term and makes the module `NotCovered`. `cps` gains the case of a lambda or
  `Rec` head applied to arguments (13, 34, and 23's lambda-headed self-call argument), only where the specialised code stays `Raw`-free (D4; S2c's refusals widened for these heads); the rest stay `NotCovered`. No
  lowering or golden change. The Goal 5 class test re-runs here.
- **Law selection by index** (D3's hypothesis; j4's encounter-order pairing is the only prior evidence): the walk
  takes the callee's law by the `idx` in the machine's term. If that fails on 13, 23 or 34, stop and report; the
  wrong-index mutants below depend on it.
- **The env-word test** (D3's hypothesis): a mutant swapping the `i32.const 0` env word with an argument word, on
  whichever of 13 and 23 the membership column keeps, must be `Rejected`, never `NotCovered`. If not, the `K::I` fallback reopens frozen rows: stop and report.
- **Done when:** Goal 2 holds for the membership column's S3 targets with asserting tests and recorded timings; Goal 5
  holds again; S3's Goal 4 set (per call site: wrong callee index, argument order, a dropped and an extra argument
  instruction on whichever of 13, 23 and 34 the column keeps, a false callee law) names each layer observed; a kernel negative exists for a call term
  at the `tatic` level; a hand-built two-callee term (one function calling two different callees, e.g. the callees of 13 and 34) proves in one
  module and swapping their indices is `Rejected` (no Goal 1 or 2 target has two callees); the held-out tests pass; no golden
  differs from S2b's and the fuzz passes; a closed self-recursive term reuses S2b's deep loop test.
- **Deletes:** nothing. j4's encounter-order pairing is not carried over.

### S4 A toy second instruction table

- **Builds.** A test-only table in `proof/tests/` whose rows carry `PrimOp` names, with at least one row named `sub`
  whose meaning no wasm row has (operands swapped, a constant added), and hand-written code lists for one or two
  straight-line terms and one mutant. Both sides read the table given, so accepting the swapped `sub` is the evidence
  that the gate reads its argument and not the wasm table.
- **Done when:** the toy table accepts its terms and rejects the mutant; its first test has leaf rows only (no `If` or
  `Call` class); `git diff --stat` shows no change to `gate.rs`, the generator or the schema in the S4 commit (a schema
  change the toy needs is its own earlier commit).
- **Deletes:** nothing; it shows the seam.

## End-state fit

| Change | Lives in | Replaces | Deletes |
|---|---|---|---|
| Row schema (three leaf classes), `Table` of classes, `prog`/`seq`/`meaning` over a table (S0, D5) | `crates/tatic-wasm/src/machine.rs` | hand-written parts of `wasm.rs` | `ctor_ty` leaf arms, `interp` literal, count literal, `seq_step` indices |
| The wasm table and printer lines (S0) | `crates/tatic-wasm/src/wasm.rs`, `ops.rs`, `print.rs` | `Ins` leaf variants | those variants, the printer's panic arms |
| Source pairing by name; result kind from the row's class (S0, D5) | `PrimOp::name()` in `crates/tatic/src/lang/`; the wasm-table accessor in `crates/tatic/src/jit/shape.rs` | `shape::op_of`, `is_comparison`'s per-op table | `op_of`, any row handle |
| `conv` pair-memo guard (S0) | a test in `crates/tatic-kernel/src` | `countdown_invariant_is_not_exponential` | that test, `countdown`, `countdown_law`, `Dup` |
| Lowering: calls as `Ins::Call`, env words as rows, no wrapper (S2b, D1) | `crates/tatic/src/jit/lower_wat.rs` | loop wrapper, tail staging, `Raw` call lines | `$t` locals, staging code |
| Module: entries of name, slots, code for every callee the lowering emits, in registration order (S2b); source term (S3) | `CompiledFragment`, `crates/tatic/src/jit/compile.rs` | arity inside the header string | nothing |
| Printer: callee names, `return_call` for a call with an empty continuation (S2b) | `crates/tatic-wasm/src/print.rs` | `Loop`/`Br` arms | those arms |
| `Call` class over a callee index, no tail flag (S2c, D3) | `machine.rs` | `Ins::Loop`, `Ins::Br` | loop stack, `loop_law`, `timeout`, `Wasm::good`, `fuel` of `meaning`/`interp` |
| Module and `ch` that `meaning` and `Source::cps` take (S2c, D3) | `machine.rs` (type), built by the generator | the fixed `Wasm { n: N }` environment | nothing |
| Frame and `local.get` row (S2c, D2) | `machine.rs` | parameters as heap cells | the frame fold, `LocalGet`'s expansion |
| The statement builder: module fixpoint over fuel, `GoodNat`, continuation relation (S2c, D4); trusted | `crates/tatic-wasm/src/machine/statement.rs` | refl `statement` | refl path (`gate_with`, `strip_loop`, fuel 1 went in S2b) |
| The generator and walk (S2c, D4); untrusted | `crates/tatic-wasm/src/machine/sim.rs` | nothing | nothing |
| Gate: `&Table`, module, three-way verdict (S0-S2c) | `crates/tatic/src/proof/gate.rs` | `in_fragment`, hardcoded `Wasm { n: N }` | `in_fragment` |
| `Source::cps`: self-call, refusing `Raw`-bearing shapes (S2c), widened for lambda or `Rec` heads (S3) | `crates/tatic/src/proof/gate.rs` (stays; a split past 1000 lines is mechanical, the tripwire) | the fragment's `unreachable!` arms | those arms |
| Verdict wiring in `prove_install` and `try_install` (S2c) | `crates/tatic/src/jit.rs` | the `in_fragment` branch | that branch; `NotCovered` goes to `kernel_verify` |
| Each callee entry's source term (S3) | `crates/tatic/src/jit/compile.rs` (registration), read by `jit.rs` | nothing | nothing; `PartialApp` callees make the module `NotCovered` |
| Heap state (D2; `Store`/`Load` stay structural classes through S0-S2b, S2c step 1 deletes them) | nothing | `Store`/`Load`, `mu` | those, the store/load check |
| Baseline fixture (S0), no-`Raw` test, held-out tests, toy table | `crates/tatic/src/proof/tests/` | nothing | nothing |
| Deep tail loop test | `crates/tatic/src/jit/tests.rs` | nothing | nothing |
| `kernel_verify` model claim (S2b) | headers of `proof.rs`, `proof/universal.rs`, `jit.rs` doc | "the compiled code loops" | nothing |
| v0.8 findings | a new numbered tier-cycle file, indexed in `docs/tier-cycle/README.md` | nothing | nothing |

`wasm.rs`, `machine/statement.rs` and `machine/sim.rs` stay under 1000 lines (j4's `sim.rs` was 809 with the module
walk and the statement; inference that the split keeps all under). `docs/TOUR.md` changes in each commit that adds, moves or removes a module.

## Risks

- **Gate time through one statement** (D4): unmeasured at the cap in the relational form; S2's go/no-go, on a branch.
- **Proof cost on heavier self-calls:** factorial's check was the largest of the no-loop run (68 ms at n = 64,
  untimed, 27% load; `docs/tier-cycle/`, "Tail self-calls as `return_call`, with no `loop` or `br`: a spike"); S2c and
  S3 time each target, and S2's scaling probe fits the `Call` weight for covered recursive terms no target resembles (Budget).
- **`Rejected` is final** for a covered term (D4): a walk gap loses an install; the fixture catches it, and the
  predicate's `Raw`-free guarantee is caught by Goal 5's class test.
- **Untried or hypothesised:** the frame's typing (D2; S2c step 1) and the operand-free `Call` type (D3; j4 kept the sort operand; S2c step 1); selecting a callee's law by `idx` (D3; S3); one `Call` for tail and non-tail, with the printer
  deriving `return_call` from the empty continuation (D3; inference, S2c proves every target with `Call` alone; the
  printer's computation stays trusted and, for `NotCovered` terms, is guarded only by the property test, the fuzz and `verify()` samples); the env word as an ordinary word (D3; S3's swap).
- **Golden churn:** at least 29 files once, in S2b; the fuzz and the deep loop test guard behaviour.
- **Unmeasured speed:** `return_call` loops (D1; S2b's bench run) and row dispatch (D5; S0's count A/B, arms rotated
  for large-page wander, ICOUNT.md).

## Parked (added to `PARKED.md` in the commit that sets this spec `active`)

- **`LocalSet` and scratch locals.** Why: no v0.8 target writes a local (D2). Trigger: the first gate target whose body
  emits `local.set` or `local.tee` (wrapping division, the closure environment); decided against until then, except as D2's fallback: locals as
  an update chain (the spikes' form: state `(locals, heap)`, slot `i` is `$p{i}`, a fresh frame per call over a zero
  base, the caller's locals restored on return). Cost: the frame becomes that chain and the `local.get` row's builder
  changes.
- **The partial row and gcd.** Why: the decision file makes it the rung after v0.8 ("Decided: division and remainder by
  zero"). Trigger: v0.8 tagged. Evidence: the guard's cost is inside the run spread at n = 64 and gcd installs through
  the generator (`docs/tier-cycle/`, "The partial row's cost, and gcd through the generator"). Open for that rung:
  where the domain lives (the spike's `dom_of` in `jit/shape.rs` makes `eval` depend on the JIT; one lookup in `lang`
  hides a one-sided mismatch from the gate; a domain on both op and row departs from h1's "one definition").
- **Bit rows** (`wrap`, `extend`, `shl`, `or`; terms 25, 28). Why: outside v0.8's goals. Trigger: v0.8 tagged.
- **The heap relation.** Why: no v0.8 target allocates (Non-goals). Trigger: the first gate target that allocates or
  reads a record (the 7 closure-record terms, term 37). Shown, by three spikes in doc 15: the allocation pointer in the state
  decides fresh addresses without order facts ("Fresh addresses by construction: the allocation pointer in the state, a
  spike"); preserved cells cross a non-tail call as a closure-relation premise and cells derive from the code ("The heap
  across a non-tail call, and an older record: a spike"); the closure relation carries a record's invariant ("A closure
  record's cells inside the closure relation: a spike"). Open (the same sections): a cell the callee writes and the continuation reads; a record allocated before a call and read after
  it (reasoned, not run); nesting cost (a three-term address checked in 9.6 s at n = 64 against 0.18 s for one level);
  composing per-function proofs, where an `Inv` universe problem would show; term 37's loop through a closure; a frame
  rule for an abstract invariant; term 27's type-indexed relation. Decided against until the trigger: the abstract memory kept now. Re-added then: `(hp, heap)` in the state, the
  `Store`/`Load` classes with their printer lines and machine test (the spike patches hold them), and `mu`.
- **`call_indirect` and the table.** Why: the 11 table-call terms need the closure convention besides (decision file,
  "Where the code stands"). Trigger: the heap relation built, or a table-only closure target picked.
- **Nested callees.** Why: j4 rejects a callee calling another callee. Trigger: a real term whose callee calls a
  callee (or S2c keeping the explicit sort operand, with its reason).
- **A distinct `i32` kind.** Why: removed on D3's hypothesis. Trigger: the first `i32` arithmetic in a target, or S3's
  env-word swap not rejected.
- **The crate's name** (`tatic-wasm` holding the backend-independent machine). Why: renaming has no consumer yet.
  Trigger: a second real backend.

## Plan inputs (for writing-plans, not design)

Facts checked on `main` at `eba0891`; line numbers drift.

- Order: S0 deletion commit, then table+threading, then `Ins` migration; S2b lowering+printer+goldens in one commit,
  then the loop deletion; held-out commit; S2c steps 1-4 as listed, then un-ignore; S3 module gate, `cps` heads +
  env-word test, mutation set; S4.
- `crates/tatic-wasm/src/wasm.rs` (555 lines): `Ins` = `Push, LocalGet, Op, Dup, If, Loop, Br, Store, Load, Raw`;
  `ctors` builds `(0..8)` constructor types; `seq_step` has `unreachable!` on `Raw` (line 249); `Wasm::good` at 474,
  used only in `wasm/laws.rs` (238-259, 336); `well_formed` tests at 506-511 (508 and 511 build `Loop`);
  `local_get_reads_the_frame` at 517 builds the frame with `upd`.
- `crates/tatic-wasm/src/wasm/laws.rs`: `loop_law` 223, `timeout` 265, `countdown` 273, `countdown_law` 282,
  `run_by_refl` 380, `countdown_invariant_is_not_exponential` 409 (n = 24, under 2 s), `run_wasm_checks` 420.
  `tatic-kernel/src/reduce.rs` line 296 cites the doc 15 finding, not the test; the test is also named in
  `docs/superpowers/plans/2026-11-08-v07-straight-line-gate.md` and doc 15 (near line 695).
- `crates/tatic/src/proof/gate.rs` (177 lines): `MAX_GATE_TREE = 8192`; `gate` calls `gate_with(.., 1, false)`, its
  only caller; `in_fragment` returns false at `arity == 0`; `op_of` at 74, 164, 169; `is_comparison` at 52;
  `Wasm { n: N }` at 114; `well_formed(code, &[])` at 97; `Source { store, qs, r }` holds no table.
- `op_of`/`is_comparison` users outside the gate: `jit/compile.rs` 291 (comment), 294, 350; `jit/ir.rs` 248, 253;
  `proof/universal.rs` 155; `jit/lower_wat.rs` 465, 473; `jit/op_table_tests.rs` 54.
- `crates/tatic/src/jit/lower_wat.rs`: the loop wrapper at 443, `(local $t{i} i64)` at 431, the tail `SelfCall` arm at
  480 (stages through `$t`, copies to `$p`), `call $f` as `raw` at 510, `call $c{f}` at 523.
- `crates/tatic/src/jit/compile.rs`: `CompiledFragment { arity, module, needs_hp_reset }`, `Item::Func { name, header,
  body }`; the `Item::Func` and `entry()` docs name the wrapping `Loop`; `PendingCombinator::Literal(Hash)`;
  `tree_size` at 438.
- `crates/tatic/src/jit.rs`: `try_install` 208 (via `compile_specialised`), `prove_install` 280 (calls `in_fragment` at
  281), `kernel_verify` 313; module doc line 37 and doc 274 name `in_fragment`. `proof.rs` lines 29, 56, 109 and
  `universal.rs`'s `loop_val` state the IR's tail self-call as `loop`/`br`.
- `crates/tatic-wasm/src/print.rs`: `print_body(code, depth, out)` has no name context; line 34 panics on `Br(_)` other
  than 0, `Dup`, `Store`, `Load`.
- Tests that name the wrapper: `jit/compile/tests.rs#fragment_bodies_contain_no_raw` (749);
  `proof/tests/gate.rs#gate_rejects_mutations` (60; unwraps `Loop` at 93) and `measure_gate_costs` (163; unwraps at
  166); `testing/ins_mutate.rs` `Loop` arm (23). The no-loop and j4 spikes found the first two green at clean HEAD and
  red with the patch.
- `proof/tests/gate.rs`: the `LocalGet 0 -> 1` / `1 -> 0` mutations skip arity-1 terms (lines 73-83); under D2 an
  out-of-range slot is a builder failure, so the `applies` lists are re-derived. `gate_check_work_is_linear_in_the_tree`
  104, `gate_build_work_is_linear_in_the_tree` 126, `time_gate` 144, `measure_cachegrind` 233 and
  `in_fragment_rejects_the_rest` 263 all reach the refl `statement`.
- `jit/tests.rs` (771 lines): `the_gates_verdict_is_final_for_fragment_terms` 731, `fragment_terms_install` 750,
  `an_operand_if_installs_through_the_chain` 762; the fixture goes in a new `proof/tests/install_table.rs`.
- Goldens: `crates/tatic/tests/golden/` has 34 files; 29 contain `loop`, 5 are `rejects_*`.
- Every wasmtime engine is `Engine::default()` (`jit.rs` 136, `compile/tests.rs`, `lower_wat.rs`,
  `lower_wat/templates.rs`, `op_table_tests.rs`, `testing/ir_fuzz.rs`, `tests/compile_fuzz.rs`); benches use
  `JitEngine::new()`.
- `cite_check.pl` and `front_matter_check.sh` skip untracked and `docs/superpowers` files; check this file with
  `perl scripts/check/cite_check.pl . docs/superpowers/specs/2026-11-10-v08-recursion-once-design.md`.

## Review

Review: 11 rounds (1-3 by the author, 4-11 external), then a restructure, then rounds 12 and 13 (all accepted),
round 14 (one finding rejected), round 15 (all accepted) and round 16 (all accepted). Rounds 12-13 name D2, D6 and D7 as they stood then; round 14 folded D6 into D2 and
removed D7.

- Round 1: `LocalSet` with no consumer, `Dup` outliving the loop law, census numbering, non-asserting `gen_real` tests.
- Round 2: a source-map Decide group, S4's "installs" with no runtime, `op_of`'s home, deletions stated as fact.
- Round 3: j4's constructor count read as the end state, "no target touches the heap" as fact, `Wasm::good`'s users.
- Round 4 (19): tests broken by `statement`/`Loop`/fuel 1, unspecialised targets, two call variants, `in_fragment` as a
  second rule, golden accounting.
- Round 5 (21): `op_of`'s callers, one `Call` built once, the model's blast radius, Goal 3's freeze, Div/Mod, arity 0.
- Round 6 (15): the frame's test edits, the constructor count, D4's false "one conversion check", the memo guard.
- Round 7 (21): spike facts into doc 15, one baseline fixture, printer callee names, the held-out timing.
- Round 8 (20): S0's count baseline, env words moved to S2b, the cap's boundary, `Store`/`Load` consumers.
- Round 9 (24): vacuous checks on an untracked spec, a numeric go/no-go, the memo-guard run record, membership as data.
- Round 10 (15): `Call` reaching `prog`, the `Rec` peel, the code-driven walk, `tree_size`'s home.
- Round 11 (22): the callee list as name and slots, env forwarding in the tail arm, structural classes by tag, the
  env-word swap (j4 never tested it), the cap's floor, and D6 raised for the user.
- Restructure (2026-11-10): rounds 4-11 kept finding material issues because the spec had grown into a plan
  (per-commit steps, per-test lists, line numbers). It is now at design altitude; code sites moved to Plan inputs and
  were re-verified on `eba0891`; the test-fate table and golden-diff procedure went to the plan's job.
- Round 12 (11): D4's heap-based reason and its `def_eq` try, `Raw`-bearing covered terms vs the final verdict (kept
  round 5's source-only `NotCovered`; `cps`'s predicate now excludes them by source property), tail-ness as a trusted
  printer rule, the row's effect and operator-function operand (the class fixes both), Goal 1's checkpoint, the refl
  path surviving S2b, the fixture's home in S0, D6 before S0, End-state rows for `cps`, the verdict wiring and module
  assembly.
- Round 13 (9, none rejected): `return_call` differs in meaning from `call` (D3's false sentence; tail-ness is now D7,
  proved or trusted), the cost bound on recursive terms (scaling probe, Budget), callee list and module as one concept
  from S2b, `push` and `local.get` as rows of one 0-to-1 class, the membership column over every Goal 1 and 2 target,
  the `Raw`-free predicate moved to S2c, the freeze ending at S3 with the held-out terms in Goal 5's set, the D2 x D6
  table, a named two-callee term for S3.

- Round 14 (10, one rejected): the hook record `meaning` takes and who builds the module fixpoint (D3, End-state
  row; fuel's replacement named); the trusted statement split from the untrusted walk, with statement mutants in Goal
  4; D7a's undercounted cost, with the tail flag deleted instead: `return_call` is a call with an empty continuation,
  derived by the printer (the trust in the printer's computation stays, stated; the IR needs no change; goldens with a
  tail known-callee call also change); D7 and its stage contradictions removed with it; the refl path no longer a
  fallback (a no-go amends Goal 5's cap); D2 x D6 collapsed into one shape, the alternatives Parked; Goal 1 targets
  versus the recursive bound (a cost knob set above them, `Call` bound in D4's `NotCovered`). Rejected: deleting
  `Store`/`Load` in S0 rather than building them as rows: `local.get` is `push; load` and the tail loop writes `$p`
  until S2b and the frame step, so the rows are needed while the goldens stay byte-identical; S0 now says so.

- Round 15 (8, none rejected): the leaf-class set (three classes; the result kind lives in the class, so `is_comparison`
  and `Op::kind()` become lookups of it; `Store`/`Load` stay structural classes until S2c instead of temporary rows,
  so S0's rows are push and the word-valued and bit-valued binary ops, which also settles the memory-class finding);
  the printer's tail-ness check as a property test, with the fuzz and `verify()` samples named as the only guard for
  `NotCovered` terms; `env` dropped from the hook record (callee laws are indexed by position, the module is the one
  concept); one budget (nodes plus a weight per `Call`) in place of the cap plus a recursive bound, and `cps` itself
  as the coverage test in place of a separate predicate; the fixture split (census rows in S0, held-out rows with the
  held-out commit); S2b assembles every callee entry and S3 adds only source terms; D2's fallback (the update chain).

- Round 16 (6, none rejected; each verified against doc 15 and the goldens): the walk's matching stated (kernel-term
  shape, spiked; the anti-goal reworded to doc 15's claim) and law selection by `idx` named as new in S3 with a stop
  condition; D2 and D3 reconciled on the explicit sort operand (j4 always kept it; the operand-free `Call` is a
  hypothesis tested in S2c step 1, in Risks); the cap floor made a clause of Goal 5; a Goal 3 failure stops the
  builder for the user (fork rule); Goal 1 targets required single-entry (checked: their specialised goldens hold one
  `func`) with a single-entry test in S2b's membership column; S2b's cap test stated as node count only, with a second
  budget check after the `Call` weight is fitted.

Rejected findings that explain a choice: a code-side `NotCovered` stop (round 5: a mutated list for a covered term
would install through `kernel_verify`); replacing the memo test with the `doubling` guards (round 7: with the memo off
they still passed, being too small); merging S2b's goldens into S2c (round 8: it would put 29 goldens into the largest
commit); deleting the heap state outright (round 11: an architectural cut, so D6).
