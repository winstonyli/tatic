---
status: draft
---

# The proved loop form: a restart instruction in the machine

Goal 1 (a JIT on proved equivalence). This spec reopens D1 of the v0.8 spec
(`docs/superpowers/specs/2026-11-10-v08-recursion-once-design.md`, "D1 No `loop`; tail calls are one `Call`, printed
`return_call`") with a measurement D1 did not have. The design came from a survey of how the kernel could take over
this optimization instead of the printer hard-coding it (2026-11-12, o1). A spike checked its central claim
(`docs/tier-cycle/`, "v0.8's build: measurements and checks", the Set and Br spike and its O3 follow-up).

## Intent and why

v0.8 prints a tail self-call as `return_call`. wasmtime compiles that as a jump back through the function's prologue,
which re-runs the stack-limit check every iteration. The cost is 1.5 ns per iteration, against 0.25 ns for a wasm
`loop`. This holds on wasmtime 42, 50.0.1 and 51.0.0-rc.1, and no `Config` setting helps. In the bench, the closure
loop's warm call went from 4.4 to 25 us when v0.8 dropped `loop` (same section, "Why", "Newer wasmtime does not fix
it").

h4, a printer-only fix, recovers about 4x. It trusts one more printer rule ("a tail `Call(own)` prints as
`local.set`s and `br`"), and its printed text is no longer the form the kernel proved. This design instead gives the
machine the two instructions the loop text is made of, `Set` and `Br` (Shape A). Each printed line is one
instruction whose meaning is proved like every other instruction's. The choice to use it moves to the untrusted lowering, where the gate
checks it on every covered install. Against h4, the trusted base gains the new meanings and their print lines, and
loses nothing. What that buys: the restart of a covered loop is proved, not assumed.

What this does not do: learn anything. Which form is faster is one fact about one engine, and that fact has not
flipped on any version measured. Learning the choice belongs to `PARKED.md`, "Learned target-cost model". This
design meets its amended trigger in form (two proved forms of one term, with an engine-caused gap), but the item
stays parked. Re-trigger: an engine version where `return_call` and `loop` run within noise of each other
(wasmtime#8135 landing), or a second proved form pair. A micro-benchmark at first use per engine version was
considered and rejected: it is one bit with a timing harness to maintain.

## Goals

- A gate-covered self-tail-recursive function installs as a wasm `loop` whose text the gate proved: `local.set` of
  each parameter in reverse, then `br $top`, inside `loop $top (result i64)`.
- `capturing_closure_loop`'s warm call returns to about its v0.7 speed (4.4 us at n = 20 000), within the bench's
  noise. A timed run confirms it.
- The trusted base grows by the two instructions' meanings and print lines, the restart field `G::bm` fills, and the
  loop wrapper in the function scaffolding. Nothing specific to the optimization is trusted.

Milestone (accepted 2026-11-12, `ROADMAP.md`): v0.9 **Proved loop form**: "a self-tail-recursive function installs
as a wasm loop whose text the kernel proved, and runs at the v0.7 loop's speed."

Decisions (2026-11-12): Shape B is B1. Shape A is A1 with `Br` typed like a call (O3): a spike of O3 accepted the
same lists and rejected the same mutants at the same cold-check cost (`docs/tier-cycle/`, "v0.8's build: measurements
and checks", "`Br` typed like a `Call`").

## Non-goals

- General loops, nested loops, or a `br` to anything but the function's own entry. Fuel stays the module fixpoint's;
  a second fuel would bring back the v0.7 loop law.
- `local.set` to a slot that is not a parameter (temporaries). `PARKED.md`, "LocalSet and scratch locals", keeps the
  temporaries binder parked.
- Proving `NotCovered` terms. They get the loop text too (Shape B), with the trust they have today.
- A learned or measured choice between the two forms (Intent).

## Anti-goals

- No peephole in the printer: each instruction prints on its own line or lines, with the existing tail rule as the
  only exception.
- No change to the proof generator (`machine/sim.rs`), the gate (`proof/gate.rs`) or the kernel. Both spikes needed
  none.

## Constraints

- Trusted: the rows (now including `local.set`) and the machine's meanings (now including `Br`). Also the statement
  builder (`G::bm`, which fills the restart field), the printer with its loop wrapper, and `source_fn`. Untrusted: the
  lowering (including its loop-form pass), `sim.rs`, and the proof generator.
- The machine frame is padded to the module's width, but the printed function declares only `$p0 .. $p{arity-1}`
  (`print.rs#print_func`). So a frame slot is a wasm local only below the record's arity, and the meanings below
  match wasm only through a `shape_check` bound on the record's arity. `local.get` relies on the same kind of bound
  today; `Set(i)` needs `i < arity`. wasmtime's validation, which `try_install` runs before the gate, would also
  refuse a `local.set` to an undeclared local. That is defence in depth only, since the gate can also be called on
  its own.
- Under that bound, each meaning is faithful to its wasm text, with no tail condition. `Br` skips what follows, and so does wasm's `br`. The tail rule only decides whether the gate *accepts* (completeness), never
  whether an accepted list is right.
- `shape` types `Br` as a call with no arguments: it pushes one word. wasm's `br` never falls through, so the code
  after a `Br` is dead in the printed text, and the meaning ignores it too. The pushed word is a typing device only:
  it lets an arm ending in `Br` meet the one-word arm rule, and a surplus word left before a `Br` fails that rule
  unless dead code after the `Br` consumes it. Dead code after a `Br` that `shape` accepts (`[Br, get 0, add]`,
  `[konst 1, Br, add]`) is valid wasm, since the operand stack is polymorphic after `br`, and it is faithful, since
  both sides skip it.
- `prog` and `put` assume `shape_check` ran (they assert on an out-of-range slot); the gate always runs it first.

## Shapes

### A The instruction shape (decided: A1 with O3)

Searched: six shapes were tried.
- A3, a row-class schema (`Class` described by pops, push and operand kind). It kept `Class` and added an `Operand`
  type, so the arms moved rather than disappeared. Removed.
- `Set` and `Br`, the spiked shape. Kept as A1.
- One terminal instruction, `Restart(n)`, in place of the `Set`s and `Br`. It removes `Class::Set`, the `local.set`
  row and the setter. Kept as A2. Its `n` could be dropped, but only by threading the own position through `prog`,
  `shape` and `seq`.
- `Set` as a structural `Ins::Set(i)` with its own constructor, not a row. It deletes `push()`, `takes_operand` and
  the row, but adds an arm to `shape`, `seq_step` and `print_body` and a constructor. Rejected: `local.get` is a row
  (class `Const`, slot operand), and keeping `local.set` a row keeps the pair symmetric in the table, the vocabulary
  the kernel works over. A bound by class instead of by name cannot work: `Const` also holds `const`.
- `Br` typed like `Call` (O3): `Ctor::Br : Pi A. F (V, A) -> F A`, pushing one word whose continuation the meaning
  ignores. Against a terminal `Br : Pi A. F A` it removes `shape`'s `Option` result, the "`Br` is last" and "both arms
  end in `Br`" rules, and `out_stack`'s empty-stack stand-in for a `Br` path, and the loop-form pass preserves shape
  (`Call(own)` and `[Set.., Br]` both pop the arguments and push one word). Spiked and folded into A1.
- A2 re-tested under O3: a `Restart(n)` typed exactly like `Call` would make the pass a rename and delete `Class::Set`
  and its row, setter and slot bound. Two objections survive and are the whole reason A1 stays: the argument order
  would live only in the printer's n-line print, where the gate cannot see it, and its frame-plus-continuation term is
  unspiked (A2 below).
- A4, a terminal call family, `TailCall(j)`, putting tail position in the instruction. It deletes the printer's tail rule
  and `map_tail_calls`. Rejected: the lowering would have to know tail position (B2). Also, unless the own-position
  case stays a proved restart, the printer would choose the loop text, which is h4's trust.

- A1 **`Set` as a row class, `Br` as a structural constructor** (recommended; the spike's shape).
  - `Class::Set` sits beside `Const`, `Word` and `Bit`. `Class::kind() -> K` becomes `push() -> Option<K>`, since
    `Set` pushes nothing. `shape`'s operand rule reads `Class::takes_operand()`, which is true for `Const` and `Set`.
  - `Ins::Br` and `Ctor::Br : Pi A. F (V, A) -> F A`, typed like a call with no arguments (O3).
  - Pro: each printed line is one instruction with its own proved meaning. The order in which the arguments reach the
    parameters is part of the list, so the gate checks it. The spike rejected forward-order `Set` mutants. The spikes
    proved the whole shape: 5 targets accepted (6 with O3, `held_out_b` added), 54 mutants rejected.
  - Con: a fourth arm in each `match Class`. `Set` is not the tripwire's third same-shaped item: it pops 1, pushes
    nothing and takes a frame operand.
- A2 **`Restart(n)`**: one terminal instruction meaning "pop `n` words, build a fresh frame as `Call` does
  (`unpack`), and restart with the activation's continuation". It prints `local.set $p{n-1}` .. `local.set $p0`,
  `br $top`.
  - Pro: against A1 it deletes `Class::Set`, the `kind`-to-`push` change, `takes_operand`, the `local.set` row,
    `setter_ty`, `put`, `setter`, the `Set` slot bound (one `n == arity` check replaces it), and about half the
    mutants. The pass becomes a rename. `PARKED.md`, "LocalSet and scratch locals", stays wholly parked.
  - Con: the argument order (stack top to `$p{n-1}`, down to `$p0`) lives only in the n-line print, where the gate
    cannot see it. A printer that emitted `$p0` first would swap the arguments under a passing proof. That is the
    printer trust this design exists to remove, scaled down to one rule.
  - Con: unspiked. Its gate term joins `unpack`'s frame with the `Br` continuation `env fr mu k`, and that pairing
    has never been walked. It is not "today's `Call` term": a tail `Call` passes a fresh continuation.
  - If A2 is ever wanted, its spike needs an order-sensitive check: a two-parameter tail loop whose result changes
    when the arguments swap, run under wasmtime against `eval`.
- Rejected: A3, the row-class schema, and A4, `TailCall(j)` (see Searched).

### B Where the loop form is chosen (decided: B1)

Searched: tried making the lowering decide tail position itself (a `tail` flag threaded through `node`). That is a
second definition of "nothing follows to the function's end", beside the printer's. Removed: the pass reads the
printer's rule.

- B1 **An untrusted pass after lowering, on the printer's tail rule** (recommended).
  - After a function lowers, a pass rewrites every `Call(own)` that the printer's tail rule marks as tail into
    `[Set(arity-1), .., Set(0), Br]`.
  - The rule is one traversal in `print.rs`. `print_body` and the pass both use it, so "tail" has one definition
    (Details, "Tail rule").
  - It runs for every function, covered or not.
  - Pro: no second tail definition. A narrower rule is fail-safe (a leftover tail self-call prints `return_call`).
  - Con: the dead env pushes below (parked).
- **Precondition: a `Call(own)` comes only from a `SelfCall`.** `br` keeps `$e*` and `$env`, while `return_call`
  passes the callee's new env words. The two agree because `SelfCall` forwards its env unchanged
  (`lower_wat.rs#Lowering::node`, `SelfCall`). A `CallKnown` to the function's own position could push other env
  words, but none reaches the pass:
  - `ir.rs#check_acyclic` rejects any combinator `$cN` that reaches itself.
  - `CallKnown` targets only lifted combinators (`ir.rs#lifted`), and the entry sits at position `n`, past them.
  - `lower` runs only after `ir::check` (`compile.rs#try_compile`).
- **Env words.** A closure with captures (`Params(k > 0)` or `Pointer`) pushes its env words before a self-call's
  arguments. The pass leaves them: the `Set`s take the arguments, and `br` discards the words below them, which wasm
  allows. All such entries are `NotCovered`. Dropping the dead pushes would need the lowering to know tail position,
  which B1 avoids. Parked, with a trigger: a profile showing the pushes.
- **Scratch locals.** `$envtmp`, `$papenv`, `$diva` and `$divb` persist across `br`, where each `return_call`
  iteration started with them zeroed. Each is written before it is read within the one straight-line `Raw` sequence
  that uses it (`push_closure_env`, `pap_env`, `dynamic_apply`, `emit_wrapping_div`; checked by two reviewers,
  2026-11-12). So persistence cannot change a result.
- **Trust for `NotCovered` text.** `NotCovered` text gains no trust from this change. `kernel_verify` proves a model,
  not the code that runs (`jit.rs#kernel_verify`), and that model already states the tail self-call as `loop`/`br`.
  The text moves from one unproved form to another unproved form.
- **Failure class.** A wrong tail rule makes `br` skip the continuation. A wrong `return_call` fails the same way
  today, so D1's "fails safe" reasoning is unchanged. For covered terms, the gate rejects a misplaced `Br` (spike
  mutants f, c1 to c5).
- Rejected:
  - B2, the lowering's own tail flag: a second tail definition, in k1's fail-unsafe form.
  - B3, only for gate-covered functions: the lowering would need the gate's verdict first, or two lowerings. It buys
    nothing, since `NotCovered` text is no less trusted than `return_call`.
  - B4, proposing both lists and keeping a measured per-engine bit (design 4 of the survey): the bit has not flipped
    on any version measured.
  - h4, printer-only (Intent): one more trusted printer rule, and the frame argument unchecked.

## Details

- **`Set`** (`Class::Set`; row `local.set`; operand the slot `i`; line `local.set $p{i}`). It pops one word, writes
  slot `i`, and passes the new frame to the rest.
  - Meaning: `\A op rest fr st mu. split st (x, s). rest (op fr x) s mu`, with `op = setter(i)`.
  - `setter(i)` rebuilds the concrete nested-pair frame with slot `i` replaced. It reduces under whnf; the spike
    asserted the no-op prelude `[get 0, Set 0]` `Accepted` before a loop-form list (`[get 1, Set 1]` was only printed:
    `Accepted`).
  - `shape_check` bounds a `Set` operand by the arity, as it bounds `local.get`, in the same `gets` walk. That walk
    matches `local.get` by name, because its class `Const` is shared with `const`. `local.set` is matched by name
    in the same arm (`"local.get" | "local.set"`), with the same negative-operand bound.
- **`Br`** (`Ins::Br`, `Ctor::Br : Pi A. F (V, A) -> F A`), typed like a call with no arguments.
  - Meaning: `\A rest fr st mu. restart fr mu`, where `MeaningEnv.restart = \fr mu. env fr mu k` (why ignoring
    `rest` and `st` is faithful: Constraints).
  - `G::bm` fills `restart` with the entry's own previous-fuel step `env` and the activation's continuation `k`. So a
    restart consumes one fuel, as `Call(own)` does.
  - `env` is `Bm_k`'s own lambda parameter, built per entry, so in a callee `Br` restarts that callee.
- **Shape.** `shape` gains one arm, `Br` pushes `W` (Constraints); nothing else in it or its callers changes.
  `well_formed`'s doc ("runs and falls through") gains "or restarts at a `Br`".
- **Tail rule.** `print.rs` gains `pub fn map_tail_calls(code: &[Ins], f: &mut dyn FnMut(usize) ->
  Option<Vec<Ins>>) -> Vec<Ins>`. It replaces each `Call(j)` in tail position of a body with `f(j)` where that
  returns `Some`, and leaves the rest unchanged.
  - Tail position: the last instruction of a tail sequence; a body is a tail sequence, and an `If` in tail
    position passes it to both arms. Every caller starts at a body's top, so the public function takes no `tail`
    flag.
  - `print_body` and `map_tail_calls` decide it with one helper, `fn tail_at(tail: bool, i: usize, len: usize) ->
    bool`, so there is one rule (B1). `tail_rule_tests.rs#tail_rule_matches_call_everywhere_under_wasmtime` guards
    it; the pass's unit test covers the traversal's recursion into nested arms.
  - The printer cannot just print the mapped code, since non-self tail calls still print `return_call`.
  - The rewrite is one function, `loop_form(code, own, slots)` over `map_tail_calls`, in the lowering: the pass
    calls it with the reversed slots, and the mutants call it with their own slot lists.
- **Printer.** `Br` prints `br $top`. `print_func` wraps the body in `loop $top (result i64)` / `end` when the body
  holds a `Br`. The tail rule is unchanged for every other call.
- **Mutation coverage.** `testing/ins_mutate.rs` does not change: its helpers mutate the `Call` form, and the tests
  map a loop-form list back to it first (Tests). The loop-form mutants live with the gate tests.

## Tests and checks

- Definitional tests of the new meanings, in the style of `machine.rs#local_get_reads_the_frame`, in a new
  `machine/loop_tests.rs` (the inline test block would near its limit):
  - over a frame of variables (slots and terminal word), `Set i` then `local.get j` gives the written word for
    `i == j` and the old slot otherwise, for every slot;
  - a `Br` after a `Set` restarts on the whole updated frame, the terminal word included (writes to padding are
    rejected by `shape`, pinned by the ported mutants);
  - `Br` with a stub `restart` reduces to `restart fr mu`, ignoring the stack under it and the code after it.
- The O3 spike's 6 targets (the first spike's 5 plus `held_out_b`), its 54 mutants and the no-op prelude,
  ported as gate tests in `proof/tests/loop_form.rs`, each at the layer the O3 spike recorded (25 differ from the
  first spike's; `docs/tier-cycle/`, "v0.8's build: measurements and checks", "`Br` typed like a `Call`"; the
  rows are in the plan, T2). A tail self-call whose argument holds a non-tail self-call (`gate.rs#gate_accepts_mixed_tail_and_non_tail_calls`'s term) is also checked.
  After the pass, `capturing_closure_loop` and `held_out_b` gate `Accepted` with `br $top` in their text.
  - They build loop lists from the `Call` form. After the pass lands, the compiled list is already in loop form, so
    a test helper first maps it back to the `Call` form.
- Callee coverage: `proof/tests/modules.rs`'s million-iteration callee loop asserts `br $top` inside `$c0`. Exactly
  one `return_call $c0` remains: the entry's call into the callee. It stays `Accepted`. Three callee mutants: `[konst 1, add]` after the record's `If` (the
  spike's `(f)`), a `Set` past the callee's arity, and the `Set`s in forward order.
- `[Br]`, `[Br, get 0, add]` and `[konst 1, Br, add]` are `[W]` and mean `restart fr mu`; a frame flows across a join.
  The surplus-word boundary is otherwise pinned by the ported mutants.
- Dead code after a `Br`, printed inside an arm, validates under wasmtime. The printed loop's run is covered by the
  JIT's million-iteration tail loop and the callee loop (below).
- The JIT tail-loop test asserts `br $top` and no `return_call $f`.
- Env-word loops, the one argued rather than proved part (Shape B, "Env words" and "Scratch locals"): no golden or
  fuzz program has a self-tail-recursive function with captures. A new test compiles a callee loop that captures a
  value, once reached directly (`Params(k > 0)`) and once through `call_indirect` (`Pointer`), asserts `br $top` in
  its text, and runs that text under wasmtime against `eval` over several inputs, 100 000 included. It runs the text
  directly: these terms are `NotCovered`, and the JIT may not install them.
- The goldens change for every self-tail-recursive function. They are regenerated and diffed. Only these
  functions change: they gain the wrapper lines, the body is re-indented by two, and the call's lines change.
- The differential compile fuzz (`tests/compile_fuzz.rs#compiled_and_interpreted_agree_on_random_terms`) still
  passes. Its generators include tail recursion with closure payloads. It reaches the loop form by construction: `gen_tail_recursive`
  always builds a tail self-call, and `gen_program` draws it one time in four. The build confirms the reach once
  and reports the count; no committed count, since `compile_fuzz.rs` is at its size cap.
- `baseline.rs`'s verdict table (Accepted against NotCovered counts) is unchanged.
- Bench: `jit_warm_cache_hit` and `jit_cold_compile_and_verify` for `capturing_closure_loop`, and `jit_warm_cache_hit`
  for gcd, with one `run.ps1 -Timed` run per arm.

## End-state fit

| Change | Location | Replaces | Deletes |
|---|---|---|---|
| `Set` class, `local.set` row, setter | `tatic-wasm/src/machine.rs`, `ops.rs`, `wasm.rs` | `Class::kind` (by `push`), the `Const`-only operand match (by `takes_operand`) | `kind` |
| `Br`, `MeaningEnv.restart` | `machine.rs`, `machine/statement.rs#G::bm` | nothing | nothing |
| loop wrapper, `br $top`, `map_tail_calls`, `tail_at` | `tatic-wasm/src/print.rs` | the inline `last_tail` expression | nothing |
| loop-form pass | `tatic/src/jit/lower_wat.rs` | tail `Call(own)` in emitted lists | the self-tail `return_call` in printed text |
| tests | `proof/tests/loop_form.rs` (new), `modules.rs`, `gate_mutants.rs`, `jit/tests.rs`, `tail_rule_tests.rs`, goldens | the `return_call` assertions for self-loops | the `call`-traps control in `jit/tests.rs` |
| docs | D1 in the v0.8 spec gets a "Reopened" line. Also updated: the decision doc's "loop and br do not survive" line; the comments that say `loop`/`br` stands for `return_call` (`jit.rs`, `proof.rs`, `proof/universal.rs`, `ir.rs`, `gate_mutants.rs`); `docs/proven.md`'s trusted list; `docs/TOUR.md`; `PARKED.md`; `ROADMAP.md` | | |

## Open items

- O1 The gcd loop is `NotCovered` (partial remainder row). Under B1 it gets the loop text but no proof. Its bench
  moves within noise either way.
- O2 A callee loop (a self-tail-recursive function that is not the entry) is the one acceptance claim the spike did
  not cover. The plan tests it first, in T2, and stops if it is refused.
