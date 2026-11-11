---
status: draft
---

# v0.8: Recursion once (one generated simulation proof over an instruction table)

ROADMAP v0.8, Goal 1 (a JIT on proved equivalence). The shape was decided on 2026-11-10: z5, staged S0-S4, division by
zero a later partial row, the heap relation open (`docs/decisions/2026-11-10-v08-shape-and-any-backend.md`, "Decided
(v0.8 shape): z5, staged"); since then **tail calls** (k2; D1 and D3) and **the state shape** (u1; D2) are decided
(decision file, "Open for the spec: tail calls and the state shape"). The rest of D3, D4 and D5 are for approval; what
no spike settled is under "Open items". Code facts are from `main` at `eba0891`, unchanged under `crates/` to
`fb2a284`. "Inference" marks what no run showed.

**Cites.** Spikes are cited by heading of doc 15, the JIT and the target machine (index `docs/tier-cycle/README.md`);
patches are in `docs/superpowers/spikes/`, runs in `docs/runs.md`. The spikes of 2026-11-11 are w2
(`docs/tier-cycle/`, "One call rule for self-calls and callees: a spike"), w3 (`docs/tier-cycle/`, "A caller's cell
across a call to another function: a spike") and w4 (`docs/tier-cycle/`, "The kernel against forged proofs of
mutants: a spike"). **Census numbers** index the census list of `docs/tier-cycle/`, "v0.7's first steps: the census
and the emit spike": `support/samples.rs#corpus` (1-23), then `testing/test_corpus.rs`'s builders (24-38). So 1, 2,
3 are factorial, `redundant_arithmetic_recursion` and fib; 13 is `twice_inc_5`; 23 is
`tail_recursive_loop_with_pap_producing_root_self_call_arg`; 34 is `let_bound_factorial_10`.

## Intent and why

v0.7 gates the straight-line fragment on a kernel proof of the emitted instruction list (`proof/gate.rs#gate`). Every
recursive or calling term still installs on a theorem about a model of the compiler (`jit.rs#kernel_verify`), not
about the code that runs. v0.8 moves loops, self-calls and direct calls to proofs of the emitted code, through one
simulation statement and one proof generator, over a machine whose instructions are rows of one table. The table is
also the seam for "any backend" (decision file, "Any backend: provided or explored, one trust story").

The spikes say this carries real terms: the generator proves both sum loops, factorial,
`redundant_arithmetic_recursion` and fib from tatic's terms against the lowering's code, with no per-function case
(`docs/tier-cycle/`, "The generator on tatic's terms and the lowering's code: a spike"); tail self-calls need no
`loop` or `br` (D1); one call constructor, callee laws as hypotheses and registry pairing carry 13, 23, 34 and
two-callee terms (D3); a frame passed in beside one opaque memory proves every real target (D2), and on it the
self-call and callee rules merge into one (w2).

## Goals

From the decision file's z5 "Done when" and ROADMAP's v0.8 line, refined:

1. Both sum loops (`capturing_closure_loop`, `partial_application_loop`) and census 1, 2, 3 install from emitted code
   through the generator, in their specialised form (the term and code `jit.rs#try_install` proves via
   `compile_specialised`), each within the budget. The gate's verdict is final for them. All five are mandatory and
   single-entry modules (their specialised goldens at `eba0891` hold one `func`). S2b's checkpoint stops if any is
   excluded or has a second entry; the `Call` weight (Budget) is set so they stay under the budget, never over.
2. Direct calls 13 and 34, and term 23, install the same way, in specialised form. A target whose specialised code
   still has a heap, table or `local.set` line (S2b's no-`Raw` test) is `NotCovered` because `cps` answers `None` for
   it (D4), stays on `kernel_verify` and gets a `PARKED.md` entry; it does not shrink silently.
3. Two functions written without sight of the generator prove against it once frozen (S2c, "Held-out terms").
4. A mutant per row and per call site is rejected, each test naming the layer that rejects it (stack check, the walk's
   `Rejected`, or the kernel). For every mutant whose statement differs from the positive case's (code and source
   mutants), a forged-proof check (one helper per stage's mutant set) asserts the kernel rejects the positive proof
   against the mutant's statement (w4's method). A registry-entry swap states the same proposition (D3, Evidence): its
   test names the pairing check or the walk's head-and-body check. A kernel negative exists for a self-call term and
   for a call term at the `tatic` level. A statement mutant (a relation that ignores the continuation, one that drops
   the fuel quantification) makes the generator's proof of a self-call term fail in the kernel.
5. The five v0.7 fragment terms still install and the v0.7 mutations are still rejected; every term of the baseline
   fixture (below) installs, or fails to, as it did at `eba0891`. Its rows whose proved code (the form `try_install`
   proves) holds a `Raw` or heap line are the `Raw`-bearing class: their verdict must be `NotCovered`, so `cps`
   regresses none. The cap keeps its floor: `doubling(12)` still installs through the one statement within S2c's
   go/no-go time (Budget).
6. Deleted: the loop machinery and the tail fact (k2), the memory rows (u1) and the hand-written machine laws, as each
   stage's Deletes lists them (End-state fit maps them to rows).
7. A toy second instruction table passes a straight-line term through the unchanged gate (S4; "installs" in ROADMAP
   read as the gate's verdict, since the toy has no runtime; inference from the wording, the user confirms).

**The baseline fixture** is a literal table, committed as a test first in S0 and passing at `eba0891`, with one row
per census term; the held-out commit (S2c) appends a row per held-out term, its outcome measured at `eba0891` in a
worktree. A row records whether the term installs, `stats.compiled`, `stats.specialised` and the specialised term's
`compile.rs#tree_size` (after S2b only install outcome and counts are compared). S2b adds a membership column (the
Goal 1 and 2 targets that pass its no-`Raw` test, the node-count cap and a single-entry test, each with its stage);
S2c fills a verdict column (`Accepted`, `Rejected`, `NotCovered`). No column reads `in_fragment`, which S2c deletes.

## Non-goals

- gcd and the partial row (the next rung, Parked); terms 25 and 28 (bit rows, Parked).
- Division and modulo: the wasm table has no `Div` or `Mod` row, so a term holding one is `NotCovered`; zero divisors
  stay with `kernel_verify` and `verify()`'s agreement.
- Closure records, the table and `call_indirect`, term 27, anything that allocates: they need the heap relation
  (Parked); 13, 23 and 34 are in scope only specialised. A heap: the memory is one opaque argument nothing reads (D2).
  `local.set` and the scratch locals: no v0.8 target consumes them (Parked).
- Deleting or rewriting `kernel_verify`'s model provers: they serve every term outside the grown fragment; only their
  header claims change (S2b).

## Anti-goals

- A proof written for one loop or one function: the generator walks the two sides' kernel terms in lockstep, with no
  per-function case and no match on the instruction list (`docs/tier-cycle/`, "One generator for loops and calls,
  with locals apart from the heap: a spike").
- A gate branch per program shape (one statement for every program, D4); per-row special cases in the schema (D5).

## Constraints

- **The kernel does not change.** Conversion has no eta and there is no cumulativity (`docs/tier-cycle/`, "A store at
  a run-time address across a call, the cost of `call`, and eta: three follow-ups"), so the generator passes
  continuations in the machine's own form and states lemma motives at the sort they land in (D4's `d`).
- **Trust.** Trusted: the rows, the printer (with its tail rule, D1), `Source::cps` and the source closure it hands the
  builder (D4), `Call`'s meaning, the statement builder (the module fixpoint, the fuel quantification, the law
  telescope, the continuation relation), which lives in its own module apart from the untrusted walk (End-state fit),
  and the gate's checks that decide whether and which statement exists: the code's **shape check** (its one home: the
  body runs from `[]` to `[word]`, no `Raw`, each `local.get` below its own function's width, D2 says why, every
  record's env count 0, D3 says why), the fragment and arity checks, and the registry pairing (D3). The kernel checks every proof against the statement; it
  cannot notice a vacuous or too-weak statement, so Goal 4 tests the statement with mutants. The walk's value checks
  (cell and returned values, branch conditions, frame slots, callee frame) only fail early: with them skipped, the
  kernel rejected every mutant (w4). They stay because the decision file's "Done when" wants each mutant's reason read,
  and a kernel type mismatch names no row or call site; Goal 4's forged-proof helper is the guard that they are not
  load-bearing. A row's meaning is checked against eval and wasmtime by `jit/op_table_tests.rs`,
  never by the gate. Both sides read one row, and the right side is built from the source term, never the code (v0.7
  spec, `docs/superpowers/specs/2026-11-08-v07-straight-line-gate-design.md`, sections 4 and 6).
- **Budget.** `proof/gate.rs#MAX_GATE_TREE` (8192 nodes; `doubling(12)` took 0.35-0.38 s) bounds straight-line cost
  only: factorial, about a dozen nodes, took 7.6 + 68 ms at n = 64, against about 0.05 ms per straight-line node. One
  budget covers both: a term's cost is its tree nodes plus a weight per `Call` site, and a term over `MAX_GATE_TREE` is
  `NotCovered`; a straight-line term's cap is unchanged. The weight is a cost knob, not a goal: S2c fits it so a
  `Call`-bearing term at the budget takes as long as the relational `doubling(12)` (at most 0.57 s), and every Goal 1
  target stays under; a Goal 2 target or held-out term over it leaves its goal. The cap may be raised on purpose,
  never lowered below `doubling(12)` (Goal 5); its doc comment ("largest power of two under 0.4 s") is amended if the
  cap probe passes above 0.4 s. The one go/no-go on time is S2's.
- **Deep builders** run under `tatic_kernel::grow`; checking threads use `tatic_kernel::CHECK_STACK`
  (`tatic-kernel/src/stack.rs`).
- **House guards** (repo `CLAUDE.md`) pass at every commit: size (1000 lines per `.rs`), test placement, tour, cite,
  layout, front matter, script header, stack literal, and doc index (v0.8's findings are new section files in doc 15's
  directory). `docs/TOUR.md` changes in each commit that adds, moves or deletes a module or a symbol it cites: S0's
  `machine.rs` split (its `wasm.rs` line and `LocalGet` entry), S2b's record move, S2c step 1 (`wasm/laws.rs`, the
  `LocalGet` row), and S2c's `machine/` modules and deletion of `gate.rs#statement` and `gate.rs#in_fragment`.
- **Long runs** (scaling tests, golden sweep, icount, timings) launch through `run.ps1`, timings with `-Timed`.

## Shapes

D1 and D2 record decisions; D3's tail clause is decided with D1. The others leave each one shape for approval: the
other options are ruled out by the anti-goals or by a spike, and stay as one-line rejections.

### D1 No `loop`; tail calls are one `Call`, printed `return_call` (decided: k2, 2026-11-10)

Searched: tried removing `loop`/`br` outright, since the lowering's only `loop` is the wrapper it puts around every
function, there for tail self-calls (`jit/lower_wat.rs#function`; the v0.7 gate proves `[Loop(body)]` at fuel 1, and
`strip_loop` is already dead, its one caller passing false), and the generator treats `br` and `call` as one fuel edge;
then any tail fact at all, in the IR or the instruction list. Removed with them: `Dup` (its only user is `countdown`),
the `$t` staging, fuel 1, the loop law, `strip_loop`, `SelfCall.tail`.

- **The shape.** The lowering emits env words, arguments, then `Ins::Call(callee)`, for self-calls and known callees
  alike. The IR has no tail flag: `SelfCall.tail`, its "outside tail position" check and their tests go (End-state fit,
  "IR without a tail fact"), and the lowering's two `SelfCall` arms become one.
  The printer writes `return_call` for a call when nothing follows it up to the function's end (every enclosing `If`
  last) and `call` for any other suffix. `Call`'s meaning has no tail branch: with an empty `rest` its continuation is
  the activation's own, and `call` then `end` equals `return_call` in wasm, so the gate's proof covers the printed
  text. The machine has no `Loop` or `Br`, and `meaning`/`interp` take no fuel.
- **Why the printer.** Its rule fails safe: an unknown suffix prints `call`, costing only stack depth, where a
  `ReturnCall` decided by the lowering fails unsafe. The case a wrong rule hurts (`1 + (if c then f(x) else 0)`) is
  outside what `cps` covers. The rule stays trusted; its test is exhaustive over small instruction lists, each printed
  with the tail rule and with every call as `call` and run under wasmtime, with a callee whose skipped continuation
  shows as a different value. That test, the differential compile fuzz and `verify()`'s samples are the only guards
  for a `NotCovered` term; the deep tail-loop test checks stack safety.
- **Inference, not run (O8).** The spikes used a separate `ReturnCall` constructor with a hook for the activation's
  own return continuation; no run shows the single `Call` with an empty `rest` and no hook. Without eta, an empty
  `rest` means `\v mu. km v mu`, not `km`, so "its continuation is the activation's own" holds up to `rel`.
- **Evidence (for the `ReturnCall`-plus-hook form).** Every target of the no-loop spike proved at n = 4, 24 and 64; a
  10^6-iteration tail loop returns `n(n+1)/2` while the same WAT with `call` traps; wasmtime 42.0.1 accepts
  `return_call` by default, and every engine on main is `Engine::default()` (`docs/tier-cycle/`, "Tail self-calls as
  `return_call`, with no `loop` or `br`: a spike").
- **Cost.** 29 of the 34 goldens change once (S2b; the 5 `rejects_*` hold no function); a future source loop that
  is not a self-call must be lowered as one; run-time speed of the tail loops is unmeasured until S2b's bench run.
- Rejected: keeping `loop` (D1b; a restart hook, two edge kinds and `LocalSet` with temporaries, or a loop law per
  shape: `docs/tier-cycle/`, "The sum loop proved against a source recursion: a spike"); a tail flag in `Call`'s
  meaning; a tail fact in the IR emitted as `ReturnCall` (k1; revisit if `cps` comes to cover an `If` in operand
  position); a call-then-return pair fused by the printer.

### D2 Locals as a frame passed in, beside one opaque memory (decided: u1, 2026-11-11)

Searched: under D1, removed `LocalSet`, the temporaries and the `$p`/`$t` printer split (the remaining `local.set`
lines are closure and division scratch no target reaches); then locals from the state; tried the memory (l2), kept.

- **The shape.** Locals are a frame of nested word pairs, `V^M x V`, padded with 0 to the module's width M (the widest
  parameter list in the module; temporaries widen it when `local.set` returns, Parked). The frame is passed
  into every class interpreter and never returned: `local.get i` is a 0-to-1 row whose operand projects the concrete
  frame (it reduces under whnf), failing at or past M. The shape check (Trust) bounds it tighter, by the function's
  own width (its arity; D3 gives a covered function no env word), since a padding slot reads 0 in the machine but is
  no local of the printed function. `unpack` builds the callee's padded frame
  (parameters at 0..`arity`, then zeros) and binds no answer type; the caller's frame comes back
  by closure in the call's continuation. Beside it, one opaque memory argument: `G A = Fr -> A -> Mem -> R`,
  `Ret = V -> Mem -> R`. v0.8 emits nothing that reads it, so the `Store`, `Load` and `upd` rows and the store/load
  check go; the statement still quantifies the memory `mu`.
- **Evidence.** The frame spike proved every real target and rejected every control with and without the memory,
  deleted the slot machinery (stuck-slot rule, slot hypotheses, `untouched`, the motive's locals and heap binders),
  and padding covered every call shape tried (`docs/tier-cycle/`, "Locals as a frame passed in, with and without the
  memory: a spike"). With the memory made a product, the machine's types, `unpack`, call row and interpreters stayed
  byte-identical (`docs/tier-cycle/`, "The heap on the frame, behind one memory argument: a spike"), also for a cell
  kept across a call to a registry callee (w3).
- **Cost.** Every law in a module mentions M, so a wider callee changes every statement of the module; a single
  function is a one-entry module whose M is its own width. The memory's size and check-time cost are unmeasured
  (O5); undoing it is deleting one argument. The generator's heap rework is owed at the heap's rung either way: the
  walk binds the memory's parts separately, since a projection of a variable state is stuck.
- Rejected: dropping the memory (l2, the draft's D2): the heap's return would re-thread it through every interpreter,
  `rel` and the callee law; the l3 frame as spiked, keeping `Store`/`Load`/`upd` rows nothing uses; locals as an update
  chain over a zero base with a restore on return (the earlier spikes' form, whose slot machinery the frame deletes);
  `LocalSet` and the `$p`/`$t` naming now (z5's S1).

### D3 One `Call` over a module position, one call rule

Searched: tried removing the per-arity constructors and `MAXA` (removed: one constructor for every arity fits the
kernel's levels); `ReturnCall` and a tail flag (removed, D1); `Ins::Call`'s argument count (removed: arity is the
callee's); a pairing search (removed: the registry gives it by construction); the separate self-call and callee rules
of the walk (merged, w2); the sort operand (removed on a hypothesis, O1); the env word, its `i32` kind and its
machinery (removed: a covered callee is closed, called directly and never packed, so the lowering's own no-pointer
form gives it no env parameter, below).

- **The shape.** One structural class `Call`, kernel constructor `[unpack, idx, rest]` (no type operands, O1). Its
  meaning continues with the meaning of `rest`, which for an empty `rest` is the fold's own continuation. **One
  numbering:** a module of `n` callees puts callee `i` at position `i` (its registry index, printed `$c{i}`) and the
  entry last, at `n` (printed `$f`), as w2 ordered them; `Ins::Call(j)` carries the position, a self-call its own
  function's, and the printer maps `j < n` to `$c{j}` and `n` to `$f`. Callee laws are indexed by that position: a
  self-call's law is the induction hypothesis, another callee's a hypothesis that the callee's own closed proof
  discharges. That closed proof is the generator run on the callee's entry at the
  enclosing module's M (D2), with the callee's own calls as hypotheses, not a one-entry module, whose narrower M would
  not match the law. The module's entries and their pairing come from the lowering's registry (`compile.rs#build`),
  entry-to-callee and callee-to-callee alike; a copy of the registry's order in the gate would be wrong (it numbers
  head first, then callee bodies last in, first out).
- **One call rule.** The walk has three rules: return, `choose`/congruence (`If`) and call. Proving function `k`, the
  call rule reads the module's positions: `k`'s own (fuel head the induction's variable, law the hypothesis) and every
  other (fuel head the outer `N`, law the callee hypothesis). It finds the entry by the head and machine body in the
  machine's kernel term, checks the source's head, body and arity, reads the frame's pair spine, checks each parameter
  slot against the source argument and the padding against 0, then applies the entry's law. It matches on term shape, never on instruction tags.
- **How `meaning` gets its inputs.** `meaning` takes the static records, the callee environment and `ch`, an opaque
  `choose` the generator proves against and then applies to the real one (the statement uses the real `choose`,
  `None`). `Call(j)` reads record `j` for its `arity` (its stack effect) and continues into environment entry `j`,
  which the statement builder fills from the module fixpoint over fuel (`N H z B_j`, `z` the out-of-fuel answer, w2;
  `meaning` itself takes no fuel). A module entry's record carries `arity`, the env access kind, the env count (env
  words: 0 for the entry's `None`, 1 for `Pointer`'s `$env`, `env_len` for `Params`' `$e{k}`) and code; it holds no
  source term and no name: the printer labels a function by its module position (`$c{i}`, `$f`), the numbering
  `Call(j)` prints by, so a label cannot disagree with the position proved, and `compile.rs#entry` finds the entry by
  position, not by the name `f`. **No env word:** `cps` refuses captured variables and closure values (D4), so a covered callee is
  never packed and never a partial-application root: the class `lower_wat.rs#direct_only` lowers as `Params`, but for
  its `env_len > 0` filter, which S2b drops. A closed, directly called callee then has no env parameter (today a dead
  `$env`, `i32.const 0` at the call), forwards nothing, and its width is its arity. The change reaches every module's
  closed direct callees, covered or not, for approval with D3. The machine places no env word: the env kind and count
  are printer-only fields; the shape check (Trust) wants env count 0, since an env parameter would shift the printed
  slots off the frame's. The record is defined in `tatic-wasm` (`machine.rs`), which cannot
  name a `tatic` type; `CompiledFragment.module: Vec<Item>` stays in `tatic`, `Item::Func` pairing the record with,
  from S3, the source term, which the builder receives only through D4's source closure. The printer derives the
  header from the record: slot names (`$p{i}`, `$env`, `$e{k}`) from the env kind, and the four scratch declarations (`$envtmp`, `$papenv`, `$diva`, `$divb`) in every function as
  today, since closure and division code installed through `kernel_verify` uses them. The `header` string is deleted,
  so the proved statement and the printed function type cannot disagree. The generator (`machine/sim.rs`) proves
  against the builder's (`machine/statement.rs`) statement; `Source::cps` takes the same `ch`.
- **Evidence.** j4 proved 13, 34 and 23 with one constructor per call kind and explicit sort operands
  (`docs/tier-cycle/`, "Modules, one call constructor and an `i32` kind: a spike"). The registry spike proved four
  terms with two or three callees (one calling another); the generator refused a swap in all 24 cases, while the
  kernel accepts it on the three flat terms, where the statement is the same proposition (`docs/tier-cycle/`,
  "Callees paired by the lowering's registry: a spike"). w2 merged the rules on the frame: `sim.rs` 744 to 710 lines,
  every verdict unchanged, checked by a second reader.
- **Fallbacks, decided in the stage.** If the operand-free type does not type (S2c step 1), the spikes' explicit sort
  binders stay (w2's `[A, S, unpack, idx, rest]`) and a Parked line records why.
- Rejected: the dead env word placed by the machine (an `env_const` row, a frame slot at `arity`, `unpack`'s env slot,
  a call-rule check, and j4's `K::I` kind or an untested ordinary word): machinery for a word nothing reads;
  one constructor per arity up to a cap (`MAXA = 3`): capped arity, rows repeated per arity; encounter-order
  pairing (j4: a swap gives a spurious rejection); separate self and callee rules (the base's 4 rules); dropping the
  walk's value checks (fewer concepts, but a `Rejected` reason would be a raw kernel error; Constraints, Trust).

### D4 One relational statement, one law telescope, one verdict

Searched: tried removing `gate.rs#statement` (refl, fuel 1, a frame in memory) as a second statement, and removed it;
an earlier draft's "convertible-first" rule; `in_fragment` as a second acceptance rule; the law's leading numeral `d`
(kept: below); a second telescope for callee laws (removed, w2); w2's temporaries binder and `temps` field (removed:
no v0.8 function has one; `LocalSet`'s rung adds them, Parked).

- **Why one statement.** `Call` needs a relation: after a call the machine runs the rest on the machine and the source
  on the source, equal only by the induction hypothesis (`docs/tier-cycle/`, "Calls by index proved against a source
  recursion: a spike"). Under D2 the types force it for straight-line code too, since the machine's return
  continuation takes the memory and the source's does not (inference from the types). One statement for straight-line
  code is also the anti-goal's choice.
- **The statement.** Every covered term is the generator's simulation: fuel `N` with `GoodNat` and a continuation
  relation hypothesis; the proof applies the relation at the answer. A straight-line term is that relation applied
  once. Every law, the motive, the step and the hypothesis share one telescope, `d, a.., mu, km, ks, rel`
  (arguments, memory, continuations, relation; w2 without its temporaries). `d` is a numeral binder that lifts the
  induction motive to Sort3: with it dropped the kernel rejected every proof, "type mismatch: inferred Type2, expected
  Type3" (run `2026-11-11-w2-wasm-lib`), since the kernel is not cumulative. It is vestigial on callee laws and the
  entry statement. **The seam to the source:** the builder (`tatic-wasm`, which names no `tatic` type) takes per module entry a source closure over the
  telescope's variables (w2's `SrcFn` over `SEnv`: answer sort, fixpoint variable, parameters, `ch`, fuel, the
  callees' source functions by position), and builds each law's right side by calling it. `cps` returns
  `Option` of that closure: coverage is decided before the builder runs, and the closure it returns is total.
- **The verdict.** `gate` returns three answers. `NotCovered` is decided from the source plus the registry-derived
  module (arity, callee set, callee kinds), never from the emitted instruction list: `cps` answers `None`, the term is
  over the budget, or the module holds a callee the walk cannot yet take (S2c step 3: a non-entry callee until S3; S3: a
  `PartialApp` callee); it goes to `kernel_verify`. The registry is source-derived, so these are not a code-side
  `NotCovered`, which the review section rejects (a second route by program shape). There is no separate coverage
  predicate: `cps` reads a term through `jit/shape.rs#classify`, which `compile.rs#build_node` lowers by, and accepts
  only an `If` on a comparison in tail position, `SelfCall`, a parameter `Var`, `Lit`, an arithmetic `Prim` with a
  row, and (from S3) a `CombinatorCall` at exact arity with a closed head, whose body and arguments it accepts. The
  lowering emits `Raw` or heap lines only for what that excludes (captured variables, closure values, unknown
  callees, partial or over-application, division); a closed exact-arity head lowers, from S2b, to its arguments and
  `call $c{f}` (`lower_wat.rs`, `CallKnown`; D3). That reading is inference; the fixture's `Raw`-bearing rows (Goal 5)
  and S2b's no-`Raw` test check it, and an accepted shape whose code holds a `Raw` line stops the builder. For a
  covered term the gate is final: `Accepted` when the walk builds a proof and the kernel accepts it, `Rejected` when
  the code is ill-formed, holds a line the walk cannot take (`Raw`, an unknown row), the walk fails, or the kernel
  refuses. A closed term is the empty parameter fold, not a case.
- **Cost.** The straight-line gate's time through the induction wrapper is unmeasured (S2's go/no-go). A walk gap on
  correct code of a covered term loses an install `kernel_verify` gives today; the fixture catches it.
- Rejected: the refl path kept for straight-line code (D4b): two statements and a route by program shape; not a
  fallback either (a no-go amends Goal 5's cap, the user's call). Falling back to `kernel_verify` after `Rejected`: the
  walk cannot tell a wrong body from its own gap (`jit/tests.rs#the_gates_verdict_is_final_for_fragment_terms`). `d`
  only on the self-call, with a second `d`-less telescope (two telescopes).

### D5 Rows as data, the table a value

Searched: removed a `Backend` trait (the table is a value), the spike's `ops::CTRL` global (a control is a mutated
table), the constructor-count literal, structural classes as table entries (every table included the same ones), the
row handle and `shape::op_of` (`Ins` holds the row's name), the constructor type, stack effect and operator function
as row fields (the class fixes them; the name selects the operator), a separate source-operator map. One 2-to-1 class
with a result-kind field fails: the field would be a second source for the kind the constructor type reads.

- **A `Row`** is a plain record: name, meaning builder, printer line. The leaf class fixes the stack effect and the
  result kind, so a row cannot disagree with its constructor. Three classes, the leaf arms of `wasm.rs#ctor_ty` today:
  0 to 1 (one numeral operand; `push` and `local.get` are two rows, whose builders are `lit n` and the frame projection
  at `n`), word-valued 2 to 1 (`V -> V -> V`, one row per arithmetic `PrimOp`) and bit-valued 2 to 1 (`V -> V ->
  Bv_1`, one row per comparison). `Op::kind()`, `shape`'s stack effects, `If`'s bit pop, `gate.rs#operand` and
  `shape::is_comparison` (also called by `ir.rs`, `compile.rs` and `proof/universal.rs`) become a lookup of the row's
  class. A later unary row (`wrap`, `extend`) adds a class, not a field. The constructor type is derived from the
  class: `operand -> rest at the output stack -> result at the input stack`.
- **A `Table`** is its leaf rows only. The structural classes (`If`, `Call`) are the machine's own, each with a
  hand-written type and meaning, defined once in `machine.rs`; the constructor order (leaf rows by class, then the
  structural classes) is derived in one place, so every table, the toy's too (S4), has the same `If` and `Call`. An
  `Ins::Row` whose name the table lacks is `Rejected`. A backend needing another structural class is a Decide then.
- **The source pairing is a name.** `PrimOp::name()` (new, in `lang`) is the key; `Source::cps` and the lowering find
  the row by it, and a name with no row is a `None` from `cps`. `tatic-wasm` knows no `PrimOp`, so there is no
  dependency cycle. The table test checks each named row against eval and wasmtime, as it checks `op_of` today.
- **Placement** (End-state fit): backend-independent code (the gate) takes the table as a value; the wasm front end
  and lowering name the one wasm table through one accessor in `jit/shape.rs`. S0 splits `wasm.rs`: `K`, `Ins`,
  `choose`, `shape`/`out_stack`/`well_formed`, the encoders and `prog`/`seq`/`interp`/`meaning` go to `machine.rs`,
  table-driven; `wasm.rs` keeps the wasm table (its rows over `ops.rs`) and its tests, and `print.rs` stays the wasm
  printer, reading each row's printer line.
- **Cost.** `Ins` loses its named leaf variants for `Ins::Row { name, operand }`; dispatch is a lookup (S0 measures).
- Rejected: an enum with derived parts (D5b): a second table is a second enum, so the gate needs the trait the
  decision file removed. `Table<S>` generic over a source key, or `PrimOp` moved into `tatic-wasm` (reverses layering).

## Open items

Each names the stage that settles it, or the rung it waits for.

- **O1 The operand-free `Call` type.** Every spike kept explicit sort binders (`S`, `A`) that index `Call`'s result
  type; dropping them is reasoned, not tried. S2c step 1 tries it; fallback in D3.
- **O3 The statement-mutation seam.** Goal 4's statement mutants (a relation that ignores the continuation, a dropped
  fuel quantification) need a mutated statement from the trusted builder. Untried candidate: the builder takes its
  relation and fuel clause from a small record; the public entry point passes the fixed one, and `cfg(test)` tests
  inside `machine/statement.rs` pass an altered one. The form must not widen a production API or compile a test-only
  switch into the trusted module. S2c step 3 settles it; if no form meets both, the statement mutants go to
  `PARKED.md` and Goal 4 says so. w4's unchecked-walk switch is not carried (the kernel rejected its terms as it did
  the forged proofs); reopen only for a mutant a forged proof cannot reach.
- **O4 Mutual recursion.** Untested; the IR check is assumed to exclude cycles (registry spike). S3 adds a test that a
  cyclic registry is `NotCovered` or `Rejected`, never accepted.
- **O5 The memory's cost.** An unread argument in every law (D2); S2c's timed targets and the go/no-go include it.
- **O6 Spike times.** The frame and w2 times come from a busy machine, direction only; S2c times every target in one
  recorded run.
- **O8 The empty-`rest` call.** D1's single `Call` with no tail branch and no hook is inference: the call rule must
  apply the callee law with the activation's own `km`, `ks` and `rel` when `rest` is empty. S2a settles it before S2b
  deletes anything. Fallback: reinstate k1's `ReturnCall` (a tail fact in the IR, a hook for the own continuation);
  that reverses a decision, so the builder stops and reports.

## Departures from the decision file

For approval with the shapes above: its S1 (locals as a state component, `local.set` a row) is dropped under D1 and
D2; its S0 check by equality of derived and old constructor types, meanings and printed WAT becomes the existing tests
pinning both (kernel checks pin types and meanings, the goldens pin printed lines); its S3's `i32` kind for the
environment pointer is dropped, since a covered callee has no env word (D3); its "Done
when" has 13 and 34 installing, here conditional on S2b's no-`Raw` test (Goal 2).

## Stages

Every commit on `main` ends green. There is no S1 (dropped, above). The fork rule: a fallback named below is taken in the stage
and recorded in the commit and, where it leaves a gap, in `PARKED.md`; a fallback that reopens frozen code, or a stop
condition, stops the builder for the user. So does a Goal 3 failure (S2c): S3 and S4 wait for the user, who chooses
between amending the generator with a new held-out pair (the freeze reopens once) and dropping the no-per-function-case
claim as a recorded finding.

### S0 The instruction table over today's constructors

- **Builds.** The leaf instructions (push, the word-valued and bit-valued binary ops) become rows with one schema in
  `tatic-wasm/src/machine.rs` (D5); `local.get` stays today's `push; load` until S2c makes it a row. `If`, `Loop`,
  `Br`, `Store` and `Load` are structural classes in `machine.rs` with today's types, meanings and printer lines (the
  loop pair until S2b, the memory pair until S2c): they are deleted later, so no row class is built for them. S2c adds
  `Call` (D5). The table derives `ctor_ty`'s leaf arms, `interp`'s leaf vector, `seq_step`'s constructor indices,
  `shape`'s stack-effect tables and the constructor count. `gate`, `statement` and `Source::cps` take `&Table` from
  here on, which makes S4's "no diff in the gate" reachable. `Ins` leaf variants become `Ins::Row { name, operand }`; `PrimOp::name()` replaces
  `shape::op_of`.
- **First, the baseline fixture**, census terms only, committed alone at `eba0891` behaviour, without the membership
  column. **Then, a mechanical deletion:** `countdown`, `countdown_law`, their `run_wasm_checks` lines and `Dup` (D1);
  `countdown_invariant_is_not_exponential`, `conv`'s only pair-memo guard, first moves to a kernel test on a small
  shared-tail case tree.
- **Done when:** the fixture passes at `eba0891` before any other S0 change; every existing test passes and the 34
  goldens are byte-identical; the new memo guard is red with the memo lookup disabled (a recorded run, its diff kept as
  a patch) and green with it on, within a stated time bound, or a `PARKED.md` entry says the guard goes and why; row
  dispatch costs within noise by instruction count (median within 0.5% of the post-deletion baseline, or the A/A
  spread if larger; ICOUNT.md, rotated arms) on `wasm_scaling` and the gate's two linear-work guards.
- **Deletes:** the hand-written `ctor_ty` leaf arms, the `interp` literal, the count literal, `seq_step`'s per-op
  indices, the `Ins` leaf variants, `shape::op_of`, `countdown`, `countdown_law`, `Dup`, the old memo test.

### S2 The generator on `Source::cps` with self-calls

Three parts: S2a settles O8 before anything is deleted; S2b changes the lowering and needs no generator; S2c builds the
generator and the one statement.

#### S2a The empty-`rest` call probe (O8)

- **Builds.** Nothing on `main`. On a scratch worktree from w2's patch (Plan inputs), a probe edits the spike
  machine's `Call` meaning to the empty-`rest` form (the tail branch and the hook removed), applies the call rule over
  the targets and records the verdicts, with controls, as a `run.ps1` run (its `docs/runs.md` row) with the probe's
  patch in `docs/superpowers/spikes/`; S2c step 4 folds it into the findings. Targets: both sum loops,
  plus one tail loop of another step shape (say, a step of 2) built from existing rows only. Controls, each on a sum
  loop: wrong argument order, a dropped call, and the call rule applied with a wrong `km`, `ks` or `rel`.
- **Done when:** every target proves through `tatic_kernel::check` and each of the three controls is rejected. Until
  it is recorded, S2b's lowering, `SelfCall.tail` and loop-machinery commits do not start. On a failure the builder
  stops and reports (O8); nothing has been deleted yet.
- **Deletes:** nothing.

#### S2b Every call emitted, no `loop` (D1)

- **Builds.** The lowering emits every self-call and known-callee call as `Ins::Call(callee)` after its env words (the
  tail self-call gains env forwarding, absent today), with no wrapper, staging or `br`. A closed, directly called
  callee lowers as `Params` with no env parameter (`direct_only`'s `env_len > 0` filter dropped, D3), so covered code
  holds no env word; other callees' env lines and closure-record lines stay `Raw`. `CompiledFragment.module` (already
  `Vec<Item>`) is extended, not duplicated: each `Item::Func` holds the `tatic-wasm` entry record (D3), moved there in
  this stage, from the lowering's registry (`PendingCombinator::Literal`), at the module position `Call(j)` carries
  (D3's numbering: callee `i` at `i`, the entry last); the printer prints `call $c{j}` or `call $f` and the header from
  it (D3: slot names from the env kind, the four scratch declarations always, no `$t{i}`), and the `header` string
  field is deleted; `well_formed` reads it, and `gate` takes it from S2c on. `SelfCall.tail` goes with
  its check and tests (D1); the printer's tail rule and its exhaustive wasmtime test land here. Until S2c gives `Call`
  a meaning, `Ins::Call` is an instruction-list entry only: `shape` and `well_formed` give it its entry's arity as its
  stack effect, and the printer prints it. No route is added: `in_fragment` stays until S2c and accepts no `App`, so a term
  whose code holds an `Ins::Call` already goes to `kernel_verify` (one regression test: factorial and a sum loop take
  that route). The model provers state the IR's tail self-call as `loop`/`br` without reading the flag; their headers
  now say the loop stands for a `return_call`.
- **Then the loop machinery goes**, in its own commit once nothing emits it: `Ins::Loop`, `Ins::Br`, the loop stack,
  the printer arms, `gate_with` and `strip_loop`. The `fuel` parameter (of `meaning`, `interp` and the refl
  `statement`), fuel 1, `loop_law`, `timeout` and `Wasm::good` stay, inert, until S2c step 1: `wasm/laws.rs`'
  `append_law`, `if_law`, `if_good` and `run_by_refl` pass fuel, and a no-go keeps them on main. The refl `statement`
  stays until S2c step 2; `proof/tests/gate.rs` changes only where it names the wrapper.
- **Done when:** the suite passes with exactly the 29 goldens that hold a `loop` (every function's wrapper) regenerated
  and the 5 `rejects_*` goldens byte-identical; the differential compile fuzz and the printer's tail test pass; a deep
  tail loop test installs a tail sum loop, runs n = 10^6 through `jit.apply` with `stats.compiled` 1, and its
  hand-written `call` control traps; every function's printed header keeps the four scratch declarations;
  `kernel_verify`'s provers pass with only header edits; the no-`Raw` test over the specialised code of every Goal 1
  and 2 target writes the fixture's membership column (its cap test is node count only; its single-entry test must pass for every Goal 1
  target); one recorded `-Timed` before/after bench of `gcd_tail_recursion_to_loop` and `capturing_closure_loop`
  (`benches/execution.rs`) has its `docs/runs.md` row (a slowdown is a finding, not a gate).
- **Checkpoint.** If the membership column excludes any Goal 1 target, or all of 13, 34 and 23, stop and report. Goal 2
  targets excluded one by one are parked.
- **Deletes:** the loop machinery above, `SelfCall.tail`, the `(local $t{i})` declarations, the tail staging and the
  closed callee's dead `$env`.

#### S2c The frame, the one statement, the `Call` meaning and the verdict

- **Builds, in order:** (1) the frame and the memory argument (D2), with `local.get` a frame-projection row and the
  operand-free `Call` type tried (O1); nothing emitted then reads the memory, so `Store`, `Load`, `upd` and the
  store/load check go, with `wasm/laws.rs` (its laws pass fuel and its runs use `upd`) and the fuel items S2b kept;
  (2) the one statement (D4) in `machine/statement.rs` on straight-line terms, with the one law
  telescope, and the generator's straight-line walk in `machine/sim.rs` (the return and `choose`/congruence rules,
  which a straight-line term needs; no call rule yet), and `cps` reshaped to D4's seam (it takes the opaque `ch`,
  strips an optional `Rec` then `arity` `Abs`, reads through `classify` and returns `Option` of the source closure),
  together replacing the refl path; (3) `Call`'s meaning over the module (D3), the call rule added to the walk in
  `machine/sim.rs`, and `cps`'s `SelfCall` case (no `CombinatorCall` until S3), with `in_fragment` replaced by the
  three-way verdict, where a module with a callee other than the entry is `NotCovered` until S3, and the shape check
  (Trust) over the module's records (its `local.get` clause only S3's wider modules can break: a one-entry module's
  M is its arity). Steps 2 and 3 build
  one statement builder with a single module entry point; a single function is a one-entry module, and the spikes'
  per-function entry point is not carried over. Step 3 also builds the statement-mutation seam (O3) with the
  statement tests of Goal 4; (4) the closing commit, which is the freeze: the deletions below that steps 1 to 3 have
  not already made, the docs grep for the old wording (ROADMAP's v0.8 line, `PARKED.md`, the decision file's "Open
  for the spec" and its stale-D2 notes, the tier-cycle README's v0.8 claims, `docs/TOUR.md`'s prose, `docs/proven.md`),
  and the v0.8 findings (S2a's and S2b's recorded runs, S2c's timings) as new section files of doc 15.
- **Branch and main.** Steps 1 and 2 are one unit on a worktree branch, merged only on a go: step 1 deletes `upd`,
  which the refl path and the v0.7 gate still use, and step 2 (statement plus straight-line walk) replaces them, so the
  branch may be red between them; the merge is green. On a no-go main holds S0 and S2b and nothing of S2c; the branch
  is kept as the record. Steps 3 and 4 follow the merge.
- **The go/no-go (S2's).** The median of 5 `run.ps1 -Timed` runs of the relational `doubling(12)` build and check is at
  most 0.57 s, 1.5 times the refl curve's 0.38 s re-measured in the same session; it runs after step 2, on the
  branch, and decides the merge. A no-go returns to the user, who amends Goal 5's cap floor; the end state has one
  statement. Step 3 builds the budget with the `Call` weight (Budget) at 0; after it a second probe fits the weight to
  that median on a generated family of self-recursive terms with 1, 2, 4, ... call sites, timed through `run.ps1
  -Timed`, in a commit before step 4. If the weight puts a Goal 1 target over the budget, lower it and record why; if
  a Goal 1 target alone checks slower than that median, stop and report. The linear-work guards keep their 2.05 bound.
- **Held-out terms.** Before step 1, a subagent given only the shape this spec says `cps` takes writes two terms
  outside the goals (say, a two-parameter non-tail recursion and a tail loop of another step shape), within the
  budget and with no `Raw`; their builders and fixture rows are committed before step 1. The tests asserting
  `Accepted` are committed at step 3, ignored, from the fixture rows (a test-only commit). The freeze is every
  non-test file under `crates/` at step 4 and ends when S3 starts; un-ignoring touches only test paths, and a failure
  is Goal 3 failed (fork rule). The held-out terms join Goal 5's regression set.
- **Done when:** Goal 1, Goal 5 and S2c's Goal 4 set hold with asserting tests; the fixture's verdict column is filled;
  the targets are timed in one recorded run, and the weight's fit and each target's cost are in the findings, every
  Goal 1 target under the budget; every golden is byte-identical to S2b's; the docs grep of step 4 is reported; Goal 3
  holds after the freeze. S2c's Goal 4 set: v0.7's `gate_rejects_mutations` carried to the one statement over the five
  fragment terms plus factorial; one operator-swap mutant per `Op` row; an `If`-arm swap (the control the deleted
  `if_law` carried); per self-call site the argument index, order, a dropped or extra argument and a dropped call; the
  no-loop spike's list minus its `return_call`-for-`call` mutant, which no `Ins` list can state; w4's real-term
  controls (factorial `Mul` to `Add`, fib `Add` to `Sub`); factorial's proof against fib's statement; the statement
  mutants of Goal 4, through O3's seam; a record with env count 1, `Rejected` by the shape check. Each test names its
  layer; each mutant whose statement differs is also forged (Goal 4's helper).
- **Edge cases, one test each:** a covered term's code with a `Raw` line, or ill-formed, is `Rejected` and not
  installed; the cases `cps` cannot take (`twice`, `\f. f 1`, an `If` in an operand or condition, `a / b`) are
  `NotCovered`; gcd (`Mod`) and a `Div` by a literal zero are `NotCovered` and install as in the fixture; a closed
  straight-line term takes the gate route.
- **Deletes:** the refl path, `in_fragment` (and its `arity == 0` clause and `unreachable!` arms), the frame-in-heap
  encoding, `LocalGet`'s `push; load` expansion, `Store`, `Load`, `upd`, the store/load check, the `fuel` parameter,
  fuel 1, `loop_law`, `timeout`, `Wasm::good`, and the rest of
  `wasm/laws.rs`: `if_inv`/`Ctl`, `append_law`, `if_law`, `if_good`, `run_by_refl`, `run_wasm_checks`,
  `wasm_programs_as_kernel_data`, `wasm_scaling`, with the machine helpers only they use (`append`, `ifp`, `spec`):
  the generator proves these per-instruction facts per term, nothing outside `laws.rs` calls them, and porting them
  to the new `meaning` buys no check the Goal 4 set lacks. **Guard:** none added: the deleted items are code symbols, so the compiler fails on any use, and the docs
  grep covers prose; the closing report says so.

### S3 Modules: calls that name their callee

- **Builds**, over S2c step 3's call rule, `Call` meaning and one-entry statement: each entry's source term from the
  registry (`jit/compile.rs`); the lift of the multi-entry `NotCovered` route; the gate's registry-pairing check
  (entry to callee, callee to callee, a source term per entry; trusted); the module statement over several entries;
  and the discharge of each callee law by the callee's own closed proof at the module's M (D3), tested for a callee
  wider than its caller and the reverse. A `PartialApp` callee has no term and makes the module `NotCovered`. `cps`
  gains `CombinatorCall` at exact arity with a closed head (13, 34, and 23's lambda-headed self-call argument; D4).
  Callee-to-callee calls need no new walk rule (D3). The fixture's `Raw`-bearing rows re-run here.
- **Done when:** Goal 2 holds for the column's S3 targets with asserting tests and recorded timings; Goal 5 holds again;
  S3's Goal 4 set (per call site: wrong callee index, argument order, a dropped and an extra argument instruction, a
  false callee law; w4's case-13 controls, `call $c0` to `call $f` and `Call(0)` to `Call(n)`; in a callee narrower
  than M, a `local.get` of a padding slot, `Rejected` by S2c step 3's shape check (D2)) names each layer observed, each
  mutant whose statement differs forged too (Goal 4's helper); a kernel negative exists for a call term at the
  `tatic` level; a two-callee term (the registry spike's shapes) proves in one module, swapping its `Call` indices is
  `Rejected` (its forged proof too) and swapping its registry entries is refused by the layer Goal 4 names; O4's cyclic-registry test passes; the held-out tests pass; no golden differs from S2b's and the fuzz
  passes.
- **Deletes:** nothing.

### S4 A toy second instruction table

- **Builds.** A test-only table in `proof/tests/` whose rows carry `PrimOp` names, with at least one row named `sub`
  whose meaning no wasm row has (operands swapped, a constant added), and hand-written code lists for one or two
  straight-line terms and one mutant. Both sides read the table given, so accepting the swapped `sub` is the evidence
  that the gate reads its argument and not the wasm table. One of its terms holds an `If` (the machine's, D5).
- **Done when:** the toy table accepts its terms and rejects the mutant; `git diff --stat` shows no change to
  `gate.rs`, the generator or the schema in the S4 commit (a schema change the toy needs is its own earlier commit).
- **Deletes:** nothing; it shows the seam.

## End-state fit

| Change | Lives in | Replaces | Deletes |
|---|---|---|---|
| Row schema (three leaf classes), `Table` of leaf rows, the machine's structural classes, and from `wasm.rs` `K`, `Ins`, `choose`, `shape`/`out_stack`/`well_formed`, the encoders, `prog`/`seq`/`interp`/`meaning` over a table (S0, D5) | `crates/tatic-wasm/src/machine.rs` | those items in `wasm.rs` | `ctor_ty` leaf arms, `interp` literal, count literal, `seq_step` indices |
| The wasm table (rows over `ops.rs`) and its tests; the wasm printer reading row printer lines (S0) | `crates/tatic-wasm/src/wasm.rs` (only the table left; size inferred well under 300 lines), `ops.rs`, `print.rs` | `Ins` leaf variants | those variants, the printer's panic arms |
| Source pairing by name; result kind from the row's class (S0, D5) | `PrimOp::name()` in `crates/tatic/src/lang/`; the wasm-table accessor in `crates/tatic/src/jit/shape.rs` | `shape::op_of`, `is_comparison`'s per-op table | `op_of`, any row handle |
| `conv` pair-memo guard (S0) | a test in `crates/tatic-kernel/src` | `countdown_invariant_is_not_exponential` | that test, `countdown`, `countdown_law`, `Dup` |
| Lowering: calls as `Ins::Call`, no wrapper, one `SelfCall` arm, closed direct callees as `Params` with no env word (S2b, D1, D3) | `crates/tatic/src/jit/lower_wat.rs` | loop wrapper, tail staging, `Raw` call lines, a closed callee's dead `$env` | `$t` locals, staging code, `direct_only`'s `env_len > 0` filter |
| IR without a tail fact (S2b, D1) | `crates/tatic/src/jit/ir.rs` | `SelfCall { tail }` | `tail`, its check, its tests in `ir.rs`, `compile.rs`, `testing/ir_fuzz.rs`, `verify/decompile/tests.rs` |
| Module entry record (arity, code; env kind and count for the printer only), moved in S2b (D3) | `crates/tatic-wasm/src/machine.rs` | the fields of `Item::Func` in `tatic` | the `Item::Func` `header` string and `name` (the printer derives both, the label from the position) |
| Module: entries from the registry (S2b); source terms (S3) | `CompiledFragment`, `crates/tatic/src/jit/compile.rs` (`Item::Func` wraps the record plus the source term) | arity inside the header string | nothing further |
| Printer: callee names, the header from the entry record, the tail rule (S2b, D1, D3) | `crates/tatic-wasm/src/print.rs` | `Loop`/`Br` arms | those arms |
| No loop machinery (S2b, D1; the fuel items at S2c step 1) | `machine.rs`, `gate.rs` | `Ins::Loop`, `Ins::Br`, fuel 1 | the loop machinery (S2b Deletes), the fuel items (S2c Deletes) |
| `Call` class over a module position; `meaning` over the records, the callee environment and `ch`, no fuel (S2c, D3) | `machine.rs` | the fixed `Wasm { n: N }` environment | nothing further |
| Frame, `local.get` row, opaque memory argument (S2c, D2) | `machine.rs` | parameters as heap cells | the frame-in-heap fold, `LocalGet`'s expansion, `Store`, `Load`, `upd`, the store/load check |
| No hand-written machine laws (S2c step 1) | the generator, per term | `wasm/laws.rs` | that file and the helpers only it uses (S2c Deletes) |
| The statement builder: module fixpoint over fuel (the callee environment), `GoodNat`, one law telescope, continuation relation; takes a source closure per entry (S2c, D4); trusted | `crates/tatic-wasm/src/machine/statement.rs` | refl `statement` | refl path |
| The generator: return and `choose`/congruence rules (S2c step 2), the one call rule (step 3), three walk rules in all (D3); untrusted | `crates/tatic-wasm/src/machine/sim.rs` | nothing | nothing |
| Gate: `&Table`, module, three-way verdict (S0-S2c) | `crates/tatic/src/proof/gate.rs` | `in_fragment` | `in_fragment` |
| `Source::cps` through `shape::classify`, returning `Option` of the builder's source closure: self-call (S2c), closed exact-arity heads (S3) | `crates/tatic/src/proof/gate.rs` (a split past 1000 lines is mechanical) | the fragment's `unreachable!` arms | those arms |
| Verdict wiring in `prove_install` and `try_install` (S2c) | `crates/tatic/src/jit.rs` | the `in_fragment` branch | that branch |
| Statement-mutation seam (S2c step 3, O3) | `cfg(test)` tests inside `crates/tatic-wasm/src/machine/statement.rs`'s module, over the builder's record | nothing | nothing |
| Baseline fixture, no-`Raw` test, held-out tests, toy table | `crates/tatic/src/proof/tests/` | nothing | nothing |
| Deep tail loop test | `crates/tatic/src/jit/tests.rs` | nothing | nothing |
| `kernel_verify` model claim (S2b) | headers of `proof.rs`, `proof/universal.rs`, `jit.rs` doc | "the compiled code loops" | nothing |
| Trust doc: the three-way verdict for the `in_fragment` paragraph; the trusted list gains the tail rule and the header from the record, the frame and memory for the heap cells, and loses `loop` (S2c step 4) | `docs/proven.md` | the `in_fragment` paragraph | its `loop` and `$p0..`-header claims |
| v0.8 findings | new section files of doc 15, indexed in `docs/tier-cycle/README.md` | nothing | nothing |

`machine.rs`, `machine/statement.rs` and `machine/sim.rs` stay under 1000 lines (w2's `sim.rs` was 710 with the walk
and the statement together; inference that the split keeps all under).

## Parked (added to `PARKED.md` in the commit that sets this spec `active`)

- **`LocalSet` and scratch locals.** Why: no v0.8 target writes a local. Trigger: the first gate target whose body
  emits `local.set` or `local.tee` (wrapping division, the closure environment). Shown: `local.set i` is a row that
  rebuilds the concrete frame, and temporaries widen M (`docs/tier-cycle/`, "Locals as a frame passed in, with and
  without the memory: a spike"); the law telescope then gains w2's temporaries binder (D4).
- **The partial row and gcd.** Why: the decision file makes it the rung after v0.8 ("Decided: division and remainder
  by zero"). Trigger: v0.8 tagged. Evidence: `docs/tier-cycle/`, "The partial row's cost, and gcd through the
  generator". Open: where the domain lives (`eval` depending on the JIT, a one-sided mismatch, or op and row).
- **Bit rows** (`wrap`, `extend`, `shl`, `or`; terms 25, 28). Why: outside v0.8's goals. Trigger: v0.8 tagged.
- **The heap relation.** Why: no v0.8 target allocates. Trigger: the first gate target that allocates or reads a
  record (the 7 closure-record terms, term 37). At that rung `Mem` becomes `V x Heap` and the `Store`/`Load` rows
  return; the machine's types, call row and interpreters stay as v0.8 leaves them, and the generator binds the
  memory's parts separately (`docs/tier-cycle/`, "The heap on the frame, behind one memory argument: a spike").
  What is shown and open: the decision file's "Open: a heap relation for callees" and doc 15's index
  (`docs/tier-cycle/README.md`), w3 and w4 among them.
- **`call_indirect` and the table.** Why: the 11 table-call terms need the closure convention besides (decision file,
  "Where the code stands"). Trigger: the heap relation built, or a table-only closure target picked.
- **A distinct `i32` kind.** Why: no v0.8 target holds an `i32` value (D3 removes the env word). Trigger: the first
  `i32` arithmetic in a target.
- **The crate's name** (`tatic-wasm` holding the backend-independent machine). Why: renaming has no consumer yet.
  Trigger: a second real backend.

## Plan inputs (for writing-plans, not design)

Facts checked on `main` at `eba0891` (no `crates/` change to `fb2a284`); line numbers are left out, since they drift.

- Order: S0's fixture, memo-guard move and deletion in S0's "First ... Then" order, then table+threading, then `Ins`
  migration; S2a probe; S2b lowering+printer+goldens with the `SelfCall.tail` deletion, then the loop deletion; held-out
  commit; S2c steps 1-2 (branch), 3, weight fit, 4, then un-ignore; S3 module gate, `cps` heads, mutation set; S4.
- `tatic-wasm/src/wasm.rs` (555 lines): `Ins` = `Push, LocalGet, Op, Dup, If, Loop, Br, Store, Load, Raw`; `seq_step`
  has `unreachable!` on `Raw`; `Wasm::good` is used only in `wasm/laws.rs`; the `well_formed` tests build `Loop`;
  `local_get_reads_the_frame` builds the frame with `upd`. `wasm/laws.rs` holds every hand-written law and
  `countdown_invariant_is_not_exponential` (n = 24, under 2 s); `tatic-kernel/src/reduce.rs` cites the doc 15
  finding, not the test. `print.rs#print_body` has no name context and panics on `Br(_)` other than 0, `Dup`,
  `Store`, `Load`.
- `tatic/src/proof/gate.rs` (177 lines): `gate` is `gate_with(.., 1, false)`'s only caller; `in_fragment` returns
  false at `arity == 0`; `Source { store, qs, r }` holds no table. `op_of`/`is_comparison` users outside it:
  `jit/compile.rs`, `jit/ir.rs`, `proof/universal.rs`, `jit/lower_wat.rs`, `jit/op_table_tests.rs`.
- `SelfCall.tail`: its files are End-state fit's "IR without a tail fact" row, plus the two arms in `jit/lower_wat.rs`;
  `proof.rs` and `proof/universal.rs` do not read it. `lower_wat.rs#function` writes the header string (`$t{i}` and the four scratch locals); `jit/compile.rs` has
  `CompiledFragment { arity, module, needs_hp_reset }` and `PendingCombinator::Literal(Hash)`.
- Tests that name the wrapper: `jit/compile/tests.rs#fragment_bodies_contain_no_raw`;
  `proof/tests/gate.rs#gate_rejects_mutations` and `measure_gate_costs`; `testing/ins_mutate.rs`'s `Loop` arm (the
  no-loop and frame spikes found the first two red). `gate_rejects_mutations`' `LocalGet` mutations skip arity-1
  terms; under D2 a slot past the function's own width is `Rejected` by the shape check, so their lists are re-derived.
- The spike code to start from: `docs/superpowers/spikes/2026-11-11-merge-call-rules-spike.patch` (w2) alone: a
  `git diff` against main that already contains the frame l3 patch; applying both fails or double-applies. w3's
  `2026-11-11-callee-cell-spike.patch` and w4's `-kernel-controls-spike.patch` also contain their base; w3's footprint
  and w4's unchecked switch (not `cfg(test)`) are heap-rung and test material, not v0.8 code.
- `cite_check.pl` and `front_matter_check.sh` skip `docs/superpowers`; check this file with
  `perl scripts/check/cite_check.pl . docs/superpowers/specs/2026-11-10-v08-recursion-once-design.md`.

## Review

Rounds 1-8 (19-25 material findings each) found the spec growing into a plan; a restructure (2026-11-10) moved it to
design altitude, and rounds 9-13 found 11, 9, 9, 8 and 6. Two shapes did not converge in review and went to the user:
tail calls (decided k2, 2026-11-10) and the state shape (decided u1, 2026-11-11). The rewrite of 2026-11-11 records
both, removes what they superseded (the memory dropped in the old D2, `ReturnCall` and any tail flag, the update-chain
locals and its slot machinery, D2's fallback, the `Nested callees` parked item the registry spike answered, S3's
law-selection stop condition) and folds in w2 (one call rule, one telescope), w3 (heap rung, Parked) and w4 (the trust
split and the forged-proof tests). Rejected findings that explain a choice: a code-side `NotCovered` stop (a mutated
list for a covered term would install through `kernel_verify`); replacing the memo test with the `doubling` guards
(with the memo off they still passed); merging S2b's goldens into S2c (29 goldens into the largest commit).
