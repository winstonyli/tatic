# tatic: a tour of the concepts

tatic is a research repo with two layers. The bottom layer (`crates/tatic/src/`) is a small JIT: a tiny higher-order term language is compiled to WebAssembly (WAT is its text form, run under wasmtime), and the compiled form is installed only after a small dependent-type kernel has checked a proof that it means the same as the reference interpreter. Terms use De Bruijn indices (a variable is a number counting binders outward, so there are no names). The upper layer is the `church-bv` crate (`crates/church-bv/src/`, its tests run with `cargo test -p church-bv --lib`, entry `crates/church-bv/src/lib.rs#mod driver`). It uses the kernel as a prover for bit-vector laws: it mines rewrite rules from the laws it proves, keeps a learned table of equal-valued terms, and measures whether the rules help. The self-improvement loop and the kernel side of goal 3 live there; no GPU or model code exists yet, and nothing in `church_bv` calls the JIT. "Church-encoded" means data written as functions (a Bool is a function that picks one of two branches), so the kernel can reason about it with no built-in types.

Keep this current: any change that renames, moves, adds or removes a module, a stage of a flow or a glossary term updates this file in the same commit (rule in `CLAUDE.md#tatic`; `scripts/check/tour_check.sh` checks every cite).

Terms used below are defined in the Glossary at the end.

Cite format: a backticked file path, a hash, then a symbol (as in `crates/tatic/src/jit.rs#apply`) means the symbol appears in that file. A cite can go stale in meaning without failing the checker; when a sentence here disagrees with the code, the code wins.

## The three goals

Written in `ROADMAP.md#Goals`; status is in `ROADMAP.md#Milestones`, not here. Check new work against them.

1. A JIT on proved equivalence. Built: a term is compiled and installed only if it passes a sample battery and a kernel-checked theorem. Its type system is in `docs/types.md#The closures fragment's type system`.
2. A kernel that improves itself. Mined rewrite rules and a learned class table are built; growth of the kernel's own vocabulary through checked definitions is not (`PARKED.md#Parked work`). Goals 1 and 2 have not met in a milestone: `ROADMAP.md#Goals` says why.
3. The kernel as the knowledge-representation-and-reasoning (KR&R) tier of a cycle with a GPU model that proposes and the kernel disposes. The kernel side exists; the model and the cycle do not (`PARKED.md#Proposer and loop`, idea in `docs/tier-cycle/#Idea`, verdict interface in `docs/tier-cycle/#Interface`). A "calibrated belief layer" between model and kernel is a design note only (`ROADMAP.md#calibrated belief layer`).

## Where to look

`crates/tatic/src/` is grouped by layer: `lang/` (terms, interpreter, parser), `jit/` (compiler pipeline), `verify/` (checkers that share no code with what they check), `support/` (samples), `testing/` (`cfg(test)` only); `proof` stays at the top, and `crates/tatic/src/bin/` holds the demo and the REPL. The kernel and the PRNG are their own crates, `crates/tatic-kernel/` and `crates/tatic-rng/`.

The JIT (`crates/tatic/src/`):
- `crates/tatic/src/jit.rs`: the cache, the installation gate, wasmtime invocation. Start here to ask "why was this term not installed?"
- `crates/tatic/src/jit/compile.rs`: the fragment test, IR builder and `try_compile`. "What can the compiler accept?"
- `crates/tatic/src/jit/shape.rs`: term-shape analysis the builder and the prover share (`peel`, `classify`, `free_vars`, closure-arity inference); it emits nothing.
- `crates/tatic/src/jit/specialise.rs` and `crates/tatic/src/verify/spec_check.rs`: the untrusted specialiser and its trusted replay checker.
- `crates/tatic/src/verify/typing.rs`: the type check that keeps closures out of the entry point.
- `crates/tatic/src/jit/ir.rs`, `crates/tatic/src/verify/decompile.rs`, `crates/tatic/src/jit/lower_wat.rs`: the IR, its validation, its WAT (the module-level templates, allocator, partial-application wrapper and curried stages, in `crates/tatic/src/jit/lower_wat/templates.rs`). "How is a closure represented?" (`crates/tatic/src/jit/lower_wat.rs#Lowering`)
- `crates/tatic/src/lang/term.rs`, `crates/tatic/src/lang/eval.rs`, `crates/tatic/src/lang/syntax.rs`: terms, the interpreter that defines correct behavior (`crates/tatic/src/lang/eval.rs#eval`), and the parser.
- `crates/tatic/src/support/samples.rs`, `crates/tatic-rng/src/lib.rs`, `crates/tatic/src/testing/test_corpus.rs`, `crates/tatic/src/testing/ir_fuzz.rs`: the sample inputs, a seeded generator, shared test terms and a fuzzer for the IR. `crates/tatic/src/bin/repl.rs`: an interactive REPL. `crates/tatic/src/bin/demo.rs#main`: the demo.

The kernel and proofs. The kernel (`tatic-kernel`), the seeded generator (`tatic-rng`), `tatic-wasm` and `church-bv` (below) are workspace crates under `crates/`; `crates/tatic` is the `tatic` package that depends on the kernel, so the kernel importing anything from `tatic` is a compile error:
- `crates/tatic-kernel/src/lib.rs` declares the trusted checker's pieces: `expr.rs` (terms and builders), `stack.rs` (stack growth), `show.rs` (printers), `subst.rs` and `hc.rs` (substitution and its memos), `reduce.rs` (`whnf`, `def_eq`, `normalize`), `check.rs` (`infer`, `check`, `Ctx`, `Globals`). `crates/tatic-kernel/src/postulates.rs`: the proof-term builder. `crates/tatic-kernel/src/spaces.rs`, `crates/tatic-kernel/src/bin.rs`: storage and serialization. `crates/tatic/src/testing/independence.rs`: the test that keeps trusted files from importing untrusted ones.
- `crates/tatic/src/proof.rs`: what is and is not established. "What does the theorem actually say?" (for a term the gate does not cover it is about `denote`: `crates/tatic/src/proof.rs#denote`, not about the emitted WAT; for one it covers, `crates/tatic/src/proof/gate.rs#gate` reads the emitted body)
- `crates/tatic/src/proof/closures.rs`, `crates/tatic/src/proof/per_instance.rs`, `crates/tatic/src/proof/universal.rs`, `crates/tatic/src/proof/denote.rs`: the closure, per-instance and universal provers, the closure denotation they share (`denote.rs`), and its debug self-check `crates/tatic/src/proof/denote.rs#debug_assert_has_type`.
- `crates/tatic/src/proof/gate.rs`: the gate, the one prover whose theorem is about the emitted code: the answer `crates/tatic/src/proof/gate.rs#Verdict` (`Accepted`, `Rejected` at a `crates/tatic/src/proof/gate.rs#Layer`, or `NotCovered`, decided from the source alone), the source function the statement reads (`crates/tatic/src/proof/gate.rs#source_fn`, built from the term and the registry and never from the `Ins` list; its calls, to itself or to a closed callee at its module position, evaluate their arguments left to right), the registry pairing (`crates/tatic/src/proof/gate.rs#pairing`: each record's source term has its arity and calls the positions its code calls), `crates/tatic/src/proof/gate.rs#build` (the statement and the generator's proof, apart, from the compiled fragment's records and sources) and `crates/tatic/src/proof/gate.rs#gate`, which has the kernel check that the printed `Ins` body, run on `tatic-wasm`'s machine, simulates the source term for every fuel.

The encodings and target machine (`crates/tatic-wasm/src/`, a crate on the kernel alone that `church-bv` and `tatic` both build on; `lib.rs` holds the `mod` lines, the prelude and the test allocator):
- `encoding/` (parent `encoding.rs` re-exports the pieces): `cx` (the binder-depth builder `Cx`/`At`, telescopes `tele`, and `law`, which walks one telescope for a proof's lambdas and its statement's Pis together), `gates` (Church Bool and vector terms, gate builders), `good` (the "good" witnesses), `division` (equality, wrapping division), `proofs` (add identity, commutativity, associativity), `tables` (truth-table and BDD builders), `tests`.
- `machine.rs`: the formal target machine, backend-independent and driven by a `Table` of rows (`Ins`, `Entry` and `EnvAccess`, the stack check `out_stack` (the stack after the code; it panics on ill-formed code) and its non-panicking form `well_formed`, the shape check over a module's records `crates/tatic-wasm/src/machine.rs#shape_check`, the `Call` class (a call continues into the callee environment's entry at a module position, then the rest of the code), `Br` (`br $top`: continues into the `MeaningEnv`'s `restart`, the function's own entry again on the current frame with the activation's continuation; the code after it is dead), the program encoding `prog` and its meaning, over a frame of the function's parameters and an opaque memory that no row reads: a Const-class row's operand hands its word to a continuation, and a Set-class row's (`local.set`) rebuilds the frame with one slot replaced; `machine/loop_tests.rs` checks the write and the restart); `machine/statement.rs`: the one statement, trusted (what it means for an entry's code to simulate its source, for every fuel: `crates/tatic-wasm/src/machine/statement.rs#statement`); `machine/sim.rs`: the generator that proves it, untrusted (`crates/tatic-wasm/src/machine/sim.rs#prove`: induction on the fuel, then a lockstep walk of the two sides with a return rule, a rule for `choose` and one call rule, whose law is the induction hypothesis for the entry itself and a callee's closed proof for any other); `wasm.rs`: the wasm `table()`; `ops.rs`: the wasm rows' meaning builders and lines; `print.rs`: prints a function (`print_func`: header from its `Entry`, labels by module position) and its body of `Ins` as WAT text (`print_body`, each row by its `line`, each `Call` by the tail rule `tail_at`, `Br` as `br $top`, and a body that holds a `Br` inside `loop $top`); `map_tail_calls` rewrites a body's tail calls by the same rule.

The bit-vector library (`crates/church-bv/src/`; `lib.rs` holds the `mod` lines, shared aliases and the test allocator; `main.rs` is the `church-bv` binary; `encoding_scaling.rs`: the encoding's scaling tests that need a `Setup`):
- `machine.rs`: the carry automaton and machine proofs. "Why did a law fall back to the machine?"
- `classes.rs`, and `class_key.txt` and `held_*.txt` in `crates/church-bv/data/`: the class table, its key and the held-out laws.
- `lemma_cache.rs`, `work.rs`, `task.rs`: caching, counters, shared memo (`crates/church-bv/src/task.rs#SharedMemo`). `host.rs`: the state of the computer a timing ran on.
- `wnat.rs`, `wfold.rs`: laws uniform in the width over a W-built index, which folds where Church numerals cannot, built as kernel terms through `Cx` (induction on the index: `crates/church-bv/src/wnat.rs#ind`); `wfold` proves stream laws over that index from the machine's encoding, one position's step through `StepProof` (`crates/church-bv/src/wfold.rs#proof`).
- `uniform/`: laws proved uniformly in the bit width over the unchanged kernel, on the named tree `T` (`width.rs` is the shared vocabulary; `bitwise`, `mul`, `shift`, `symmul`, `symmul_stream` are the law families).
- `entry.rs`: the `church-bv <subcommand>` table (`sweep`, `worker`, `loop-stream`, `proof-cost-split`, `rule-set-kernel-check`, `ctx-fit`, `overlap-report`, `q1-report`) and `main` (`crates/church-bv/src/entry.rs#main`); each subcommand runs on a thread with the check stack (`crates/church-bv/src/entry.rs#run_on_thread`, as a worker's task threads and lanes do), and the binary tells `Worker` to re-enter itself as `church-bv worker` (`crates/church-bv/src/driver.rs#declare_reentry`).

The rewriter and provers (`crates/church-bv/src/`):
- `rewrite/` (the parent re-exports the pieces): `term` (interned terms), `values` (value memos and screens), `plan` (plans and the proof compiler), `rules` (rule table and admission), `rewriter` (the rewriter and its memo), `join` (bounded join, machine fallback, `prove_eq`), `laws` (`rewrite_plan`, `rewrite_law`); its tests are `rewrite/tests.rs`. `job.rs`: per-task and per-thread state.
- `streams.rs`: the law supply, operator-set streams merged per salt (`crates/church-bv/src/streams.rs#stream_sequence`) and their phase windows (`crates/church-bv/src/streams.rs#residue`).
- `search.rs`: rule admission (`crates/church-bv/src/search.rs#rule_admissible`) and cost (`crates/church-bv/src/search.rs#law_cost`), and the bodies of the two worker tasks: serving (`crates/church-bv/src/search.rs#rule_set_kernel_check_task`) and mining (`crates/church-bv/src/search.rs#rule_miner`).

External corpora (`crates/church-bv/src/`):
- `corpus.rs`: fixed lists of named expressions in the loop's term language, one `docs/corpora/<source>/cases.txt` per source with a `SOURCE.md` (origin, licence, in-scope count). `crates/church-bv/src/corpus.rs#read_cases` loads one; `crates/church-bv/src/corpus.rs#measure` reports what the class table and the rewriter do to each case (operators before, after the table, after the rewrite).

The belief layer (`crates/church-bv/src/`):
- `belief.rs`: a calibrated estimate of whether a claimed equality is refuted or unprovable, from its shape and the cheap evidence it has passed; it is meant to order and budget work (nothing reads a belief yet) and never accepts a claim. Pure statistics (`crates/church-bv/src/belief.rs#auc`, grouped folds `crates/church-bv/src/belief.rs#fold_of`) sit under the estimators, the claim dump and the report.

The miner, driver, loop and gate:
- `miner.rs` (with `miner/`): how rules are chosen. `driver.rs`: loops, sweeps, extras, workers. `scripts/gate/streams_ab.sh`: the A/B gate.
- `ctx_scorer.rs`: an offline study of ranking the miner's extras by a model that sees each law's pool context (`crates/church-bv/src/ctx_scorer.rs#q1`); it reads a pool dump the miner writes when asked (`crates/church-bv/src/miner/laws.rs#dump_pool`, `scripts/study/ctx_dump.sh`), and its fitted model (a weights file, `Model::to_text`) is what `EXTRAS_SELECT=ctx` scores the pool with at run time (`crates/church-bv/src/miner/laws.rs#ctx_pool_ranks`, `CTX_WEIGHTS`).
- `tools/runs/` (own crate): the measured-run runner and timer the gate launches its arms through.
- `scripts/` is grouped by role (`check/layout_check.sh` fails on a file left directly in it). `gate/`: `streams_ab.sh` (the A/B gate), `arm_env.sh` (the environments of its arms), `gate.sh` (untimed, with the arm cache), `ablations.sh`, `bench_ab.sh`, `curve.sh` (an arm summed over salts, using `arm_row.sh`) and `test_gate.sh`. `check/`: the repo guards `tour_check.sh` (TOUR cites), `cite_check.sh` (section cites in docs and code comments, plus `tour_check.sh`), `size_check.sh`, `test_placement_check.sh`, `doc_index_check.sh` (the indexes and file sizes of the one-file-per-section docs), `layout_check.sh`, `front_matter_check.sh` (specs and plans open with a valid `status:`), `script_header_check.sh` (every dated script under `docs/runs/*/scripts/` opens with a description: `grep -m1 -E "^(#[^!]|\"\"\")" docs/runs/*/scripts/*` lists them), each with its `*_check_check.sh` test. `study/`: the Q2 and context-scorer scripts (`q2_*.sh`, `ctx_*.sh`) and `rules/`. `experiments/` (older experiment scripts) is git-ignored and exists only on the author's machine.
- `crates/tatic/benches/`: criterion benchmarks of execution and proofs.

Test and fuzz suites (each protects one layer). In `crates/tatic-kernel/tests/`: `church_encoding.rs` and `church_lemmas.rs` (the Church-encoded kernel library), `kernel_fuzz.rs` and `kernel_soundness_fuzz.rs` (the kernel never accepts a false claim). In `crates/tatic/tests/`: `compile_fuzz.rs` (compiled code against the interpreter), `syntax_fuzz.rs` (the parser), `golden_wat.rs` with `golden/` (pinned WAT output).

Project state: `ROADMAP.md`, `PARKED.md`, `docs/tier-cycle/README.md`, `docs/learned-vs-fixed.md`, `docs/related-work/README.md` (the surveyed landscape and the implementation notes, one file per `§`).

## Running things

No commands are restated here; each has one home.
- Build, test, demo, REPL, benches, the sweep build profile: `README.md#cargo test`.
- One loop or one sweep, and every environment switch (`LOOP_MODE`, `RULEMINER_FAST`, `POOL`, `GEN_DRAW`, `ABLATE`): the module doc of `crates/church-bv/src/driver.rs#LOOP_MODE`.
- The A/B gate: the header of `scripts/gate/streams_ab.sh#arm`. Recorded runs (raw output, `docs/runs.md` rows, CPU leases): `CLAUDE.md#tatic`.

## The picture

### (a) The JIT path

1. Source text is parsed into interned De Bruijn terms (`let` is sugar for application): `crates/tatic/src/lang/syntax.rs#parse`. Terms can also be built with `TermStore` builders.
2. Every node is interned by BLAKE3 content hash; the root hash is the term's identity and the JIT cache key: `crates/tatic/src/lang/term.rs#intern`.
3. The caller invokes `JitEngine::apply`. A hit with matching arity calls the compiled function; a hit on a decline entry, or on a `Compiled` entry of another arity, is interpreted; a miss goes to step 4: `crates/tatic/src/jit.rs#apply`.
4. On a miss, `compile_verify_and_apply` runs `try_install`. A decline is cached with its reason; an argument-count mismatch is interpreted and caches nothing: `crates/tatic/src/jit.rs#compile_verify_and_apply`.
5. `compile_specialised` first tries the untrusted beta-v specialiser; its trace must be accepted by the independent checker and the result must compile, else the unspecialised term is used: `crates/tatic/src/jit/compile.rs#compile_candidate`.
6. `try_compile` rejects oversize terms, builds the closure-converted IR, runs `ir::check`, decompiles the IR and requires the source hash back, then lowers it to a module of `Item`s, whose functions are `Entry` records (arity, `EnvAccess`, a body of `Ins`) beside the registered source term at their position (`CompiledFragment::sources`) that the printer turns into WAT: every call is `Ins::Call(position)`; a tail self call is then rewritten to the loop form (`crates/tatic/src/jit/lower_wat.rs#loop_form`), and a remaining call is written `return_call` where it is the last instruction of a tail position (the tail rule) and `call` elsewhere (`CompiledFragment::wat`): `crates/tatic/src/jit/compile.rs#try_compile`.
7. The WAT is instantiated under wasmtime: `crates/tatic/src/jit.rs#instantiate`. Before that, the argument count must match and the term must pass the simple type check `crates/tatic/src/verify/typing.rs#well_typed`.
8. Layer 1 of "found equivalent": the compiled function and the interpreter must agree on a fixed battery of inputs: `crates/tatic/src/jit.rs#verify`.
9. Layer 2: a kernel-checked theorem: `crates/tatic/src/jit.rs#prove_install`. A term the gate covers (`Accepted` or `Rejected`) is decided by the gate alone, on the emitted body. A `NotCovered` term goes to `crates/tatic/src/jit.rs#kernel_verify`: a term that calls one of its own parameters is refused first (`crates/tatic/src/jit.rs#calls_a_parameter`). Then come `prove_closure_expr` and `prove_tail_recursive_universal`, which state the claim for every input; only at arity 0 is the per-instance proof (one concrete execution) also tried. Failure caches `NoUniversalProof` and the term stays interpreted. How a theorem is built is flow (c).
10. All gates passed: the entry is stored as `Compiled`, and calls go through `crates/tatic/src/jit.rs#invoke`, which zeroes the allocator pointer first.

The whole gate order is written down in `crates/tatic/src/jit.rs#try_install`.

### (b) The self-improvement loop, from stream to A/B gate

1. A deterministic list of candidate bit-vector laws is built per salt by interleaving operator-set streams: `crates/church-bv/src/streams.rs#stream_sequence`. A loop reads one phase of it (a residue class): `crates/church-bv/src/streams.rs#residue`.
2. The driver cuts a window of laws and writes it as a lawfile for a worker task: `crates/church-bv/src/driver.rs#write_laws`.
3. A sweep builds three loops (phases 1 to 3) and runs each: `crates/church-bv/src/driver.rs#run_sweep`.
4. `run_loop` serves a batch of laws under the rules in force, records the batch's M, then runs the mines scheduled after it: `crates/church-bv/src/driver.rs#run_loop`.
5. Serving: each law is rewritten, then closed by the prover cascade (flow (d)); the leftover that needed a whole-term machine proof or stayed unproved is M: `crates/church-bv/src/search.rs#rule_set_kernel_check_task`.
6. A mine may also take extras, more laws from a deeper stream sequence, filtered against served and held-out laws: `crates/church-bv/src/driver.rs#scope_extras`.
7. The mine task maps to the miner: `crates/church-bv/src/driver.rs#task_fn`. It finds the stragglers under the base rules: `crates/church-bv/src/miner/laws.rs#laws_of`.
8. It generates candidate rules from the stragglers' normal forms: `crates/church-bv/src/miner/candidates.rs#candidates`, and scores them in greedy rounds: `crates/church-bv/src/miner/rounds.rs#play`. In a sweep (`RULEMINER_FAST`) only each round's winner is proved, in the background (`crates/church-bv/src/miner/rounds.rs#Prover`); `settle` rolls back rounds built on a winner whose proof fails. Without that switch every candidate is proved first.
9. Each committed rule is recorded as chosen: `crates/church-bv/src/miner/rounds.rs#settle`; the driver appends it to the loop's rules file and the next batch is served under it.
10. The A/B gate runs a sweep for an A and a B build per salt, then scores each loop's final rules on the held-out bands and compares M, held-out M, CPU and work counts: `scripts/gate/streams_ab.sh#arm`. The held-out laws come from `crates/church-bv/src/classes.rs#held_laws`.

### (c) From term to theorem (the JIT's proofs)

1. `kernel_verify` (flow (a) step 9) calls a prover with the interned term and gets an `EquivalenceProof` or `None`: `crates/tatic/src/proof.rs#EquivalenceProof`.
2. The statement is about `denote`, the term's meaning as a kernel expression over the postulated arithmetic (`crates/tatic/src/proof.rs#denote`), not about the emitted WAT; the proof is a kernel-checked `refl` between that meaning and the compiled form's.
3. Terms with closures (and what the gate leaves `NotCovered`): `crates/tatic/src/proof/closures.rs#prove_closure_expr`. Self-recursion that tail-calls: `crates/tatic/src/proof/universal.rs#prove_tail_recursive_universal` over the postulated inductive family (Ev). Arity 0 only: `crates/tatic/src/proof/per_instance.rs#prove_closure_expr_instance`. Terms the gate covers: `crates/tatic/src/proof/gate.rs#gate`, whose statement (`crates/tatic-wasm/src/machine/statement.rs#statement`) is about the emitted body itself: the machine on `prog code` equals the source term built in continuation-passing form, for every fuel.
4. Proof terms are built with the untrusted `Postulates` builder and typed by the trusted checker `crates/tatic-kernel/src/check.rs#check_in`, so a prover bug should make a proof fail to check rather than pass a false one.

### (d) Serving one law (the rewriter and the prover cascade)

1. Entry: `crates/church-bv/src/rewrite/laws.rs#rewrite_plan` rewrites both sides, children first, then closes the pair with `prove_eq`. `rewrite_law` compiles the plan into a kernel proof.
2. Per node (`crates/church-bv/src/rewrite/rewriter.rs#rewrite_uncached`): the class table's lookup and proved step come first (a node the table knows is final), then the fixed rules, then the mined rules (`crates/church-bv/src/rewrite/rules.rs#run_order`). Everything rewritten carries a `Plan` recording why.
3. `crates/church-bv/src/rewrite/join.rs#prove_eq` closes the rewritten pair, first match wins: equal sides (refl), the bitwise truth table, the per-position check for shift terms, the bit-0 mask reduction, then `join_or_machine`: the bounded join, else the whole-term machine proof.
4. The floor is the set of laws that reach the machine; the join and the rules exist to push it down, and M counts it. See `docs/tier-cycle/#The floor and the bounded join`.
5. The random-input screen is not part of serving: it refutes a candidate law or rule before any proof is tried (`crates/church-bv/src/miner/candidates.rs#candidates`, and the class table's replacement check in `crates/church-bv/src/classes.rs#Classes`), and gates the machine and join steps with a cheap difference test.
6. A rule is itself proved before it is used: `crates/church-bv/src/rewrite/rules.rs#prove_rule` tries its own route first, then the every-input fallback.

## Glossary

- **ABLATE**: environment switch that turns a named rule or prover part off. `crates/church-bv/src/job.rs#ablated`
- **Batch**: B consecutive laws of a loop's window, served before they are mined. `crates/church-bv/src/driver.rs#run_loop`
- **Corpus**: a fixed, named list of expressions from one source, measured by the table and the rewriter. `crates/church-bv/src/corpus.rs#read_cases`
- **Belief layer**: P(a claimed equality is refuted or unprovable) from shape and evidence; meant to order and budget work (nothing reads it yet), never accepts a claim. `crates/church-bv/src/belief.rs#auc`
- **Beta-v**: contracting an application of a lambda to a value only; full beta is unsound under call-by-value with errors and `Rec`. `crates/tatic/src/verify/spec_check.rs#check`
- **Br**: the instruction `br $top`, which restarts the function on the current frame; typed like a `Call` with no arguments, it is how a tail self-call is printed as a loop. `crates/tatic-wasm/src/machine.rs#Ins`
- **Bounded join**: bounded two-sided search that rewrites both sides with the rules plus assoc/comm until they meet. `crates/church-bv/src/rewrite/join.rs#join_eq`
- **CacheEntry**: the per-hash JIT outcome; every variant but `Compiled` is served by the interpreter. `crates/tatic/src/jit.rs#CacheEntry`
- **Carry cap**: the most carries per side the machine proof takes on. `crates/church-bv/src/machine.rs#carry_cap`
- **Carry vector**: a machine's state between bit positions, one bit per carrying node. `crates/church-bv/src/machine.rs#carries`
- **Church Bool**: the kernel type `Pi C. C -> C -> C`; true picks the first branch. `crates/tatic-wasm/src/encoding/gates.rs#bool0`
- **Church bit-vector**: a continuation over n Bools, least significant bit first. `crates/tatic-wasm/src/encoding/gates.rs#bv_ty`
- **Class table**: a learned map from the value signature of a term to its smallest representative, used as a rewriting step; a replacement is used only if it is provable. `crates/church-bv/src/classes.rs#Classes`
- **Classify / Shape**: the one case analysis of a body node shared by the IR builder and the proof walkers. `crates/tatic/src/jit/shape.rs#classify`
- **Combinator**: a lambda or `Rec` lifted out as its own function (or a partial-application wrapper) in the IR. `crates/tatic/src/jit/ir.rs#Combinator`
- **Compiler (Plan to proof)**: turns a rewriter `Plan` into a checked kernel proof on demand. `crates/church-bv/src/rewrite/plan.rs#Compiler`
- **Const (postulate)**: a kernel constant typed by the `Globals` list; it never unfolds, so it acts as an axiom. `crates/tatic-kernel/src/check.rs#const_type`
- **Content hash**: BLAKE3 of a node's tag and payload; equal structure gives equal hash in any store. `crates/tatic/src/lang/term.rs#content_hash`
- **Cycle cut**: the rewriter returns a term unchanged when a term on its path embeds in it, ending growing chains early. `crates/church-bv/src/rewrite/rewriter.rs#cut_at`
- **Decompile (translation validation)**: rebuilds the source term from the IR alone so a builder bug cannot cancel itself. `crates/tatic/src/verify/decompile.rs#decompile`
- **Dispatch**: whether unknown calls are lowered fast (trap on arity mismatch) or curried. `crates/tatic/src/jit/ir.rs#Dispatch`
- **Dom**: where a row has a value: `holds` on source operands, `circuit` the same predicate as a `V -> V -> Bv_1` kernel term; the machine and the source guard every Word site with it, and bit rows are left unguarded. `crates/tatic-wasm/src/ops.rs#Dom`
- **Encoding (phi, g)**: a coarse labelling of carry vectors through which both machines factor; found by `crates/church-bv/src/machine.rs#moore_encoding`.
- **Entry / EnvAccess**: a lowered function's record: its arity, how it reaches its captures (`Params(k)` as leading `i64` parameters, or `Pointer` through `$env`) and its body; the printer derives the header from it, and the gate proves the entry's body and its callees'. A module position names a function: a combinator's index, the entry last (`$f`). `crates/tatic-wasm/src/machine.rs#Entry`, `crates/tatic-wasm/src/machine.rs#EnvAccess`, `crates/tatic-wasm/src/print.rs#print_func`
- **EquivalenceProof**: a kernel-checked refl proof packaged with its globals and arity. `crates/tatic/src/proof.rs#EquivalenceProof`
- **Every-input fallback**: a rule no other route proves is proved by case-splitting over all input bits when width x variables is at most 12; a rule past the cap stays unproved. `crates/church-bv/src/rewrite/rules.rs#EVERY_INPUT_BITS`
- **Extras**: additional laws mined alongside a loop's batch; each mine takes its own slice. `crates/church-bv/src/driver.rs#EXTRAS_N`
- **Ev / ev_rec**: the postulated inductive family and recursor behind the universal tail-recursion theorem. `crates/tatic/src/proof/universal.rs#prove_tail_recursive_universal`
- **Expr**: a Copy handle to an interned kernel term. `crates/tatic-kernel/src/expr.rs#Expr`
- **Fallback (machine)**: a whole-term carry-machine proof used when rewriting and join fail; counted toward M. `crates/church-bv/src/rewrite/join.rs#machine_fallback`
- **Floor**: the laws that still need the machine after rewriting and the join. `docs/tier-cycle/#The floor and the bounded join`
- **Free**: a builder-scope parameter the kernel refuses to type, so an escaped one cannot act as an axiom. `crates/tatic-kernel/src/check.rs#free_escaped`
- **Free share**: the share of a band's laws proved with no whole-term machine proof. `docs/tier-cycle/#Metrics`
- **Frontier**: the held-out free share per size band (11, 13, 15, 17): how far up in law size the rules still avoid the machine. The v0.6 success measure is moving it, not M on a fixed stream. `docs/tier-cycle/#The frontier and v0.5`, `ROADMAP.md#Milestones`
- **Gate (A/B)**: two builds, per salt, compared on M, held-out M, CPU and work counts; entry point `scripts/gate/streams_ab.sh#arm`. Not the installation gate.
- **GEN_DRAW**: integer that re-draws the extras from a different sample. `crates/church-bv/src/driver.rs#scope_extras`
- **Redraw spread (sigma)**: the difference between two arms that differ only in `GEN_DRAW`; the gate is deterministic, so this A/A spread is the noise floor a win must beat. A doc measure, not computed in code. `docs/tier-cycle/#The streams and the gate`
- **Globals / Ctx**: the trusted list of constant types and the local binder types. `crates/tatic-kernel/src/check.rs#Globals`
- **Good witness (GoodBool, GoodBv)**: hypotheses that let a proof split a symbolic bit. `crates/tatic-wasm/src/encoding/gates.rs#binders`
- **Guard laws**: machine-free laws scored along with stragglers so a regressing candidate is visible. `crates/church-bv/src/miner/laws.rs#Laws`
- **Held-out bands**: committed law files of sizes 11, 13, 15, 17 that no loop serves. `crates/church-bv/src/classes.rs#HELD_BANDS`
- **Held-out M**: M of a loop's final rules on the held-out bands. `docs/tier-cycle/#Metrics`
- **hp reset**: the host zeroes the bump-allocator pointer before every compiled call. `crates/tatic/src/jit.rs#invoke`
- **Independence**: a test that restricts which modules a trusted file may use. `crates/tatic/src/testing/independence.rs#assert_independent`
- **Installation gate**: arity, type check, instantiate, samples, then kernel theorem (a term that calls its own parameter is refused first); only then `Compiled`. `crates/tatic/src/jit.rs#try_install`
- **Job / Setup**: one thread's rewriting state over the per-task shared configuration. `crates/church-bv/src/job.rs#Job`, `crates/church-bv/src/job.rs#Setup`
- **Kernel**: the trusted checker; the only place typing and definitional equality are decided. `crates/tatic-kernel/src/check.rs#check_in`
- **Law**: an equation between two bit-vector terms; `crates/church-bv/src/rewrite/term.rs#Term` is the interned expression tree.
- **Lemma cache**: on-disk cache of already-checked lemma statements shared by processes of one build. `crates/church-bv/src/lemma_cache.rs#Cache`
- **Lawfile**: text file of `lhs = rhs` lines handed to a worker task. `crates/church-bv/src/driver.rs#write_laws`
- **Loop**: serve a batch, mine, serve the next batch under the new rules. `crates/church-bv/src/driver.rs#run_loop`
- **Loop form / loop-form pass**: a tail self call written as `local.set`s of the parameter slots (last argument first) then `Br`, printed inside `loop $top`; the pass rewrites every function's tail self calls to it after lowering, by the printer's tail rule. `crates/tatic/src/jit/lower_wat.rs#loop_form`
- **local.get**: the row that reads parameter slot i of the frame; its operand projects the frame by `sigrec`. `crates/tatic-wasm/src/ops.rs#local_get_row`
- **M**: per batch, the laws that needed a whole-term machine proof or were not proved; laws closed by the bounded join are not counted; lower is better. `docs/tier-cycle/#Metrics`
- **Machine**: a term turned into a bit-serial automaton whose state is a carry vector. `crates/church-bv/src/machine.rs#Machine`
- **Mined rules**: rules chosen at run time by the miner, tried after the fixed rules. `crates/church-bv/src/rewrite/rules.rs#run_order`
- **Mine**: one run of the rule miner on a lawfile. `crates/church-bv/src/miner.rs#mine`
- **Row / Table / Class**: a row is one leaf instruction (name, class, kernel meaning, printed line); a table is a backend's rows by name; a class (`Const`, `Word`, `Bit`, `Set`) fixes a row's stack effect and its constructor (`Set` pops a word into a parameter slot and pushes nothing). The lowering emits `Ins::Row { name, operand }` and prints the row's line; the machine runs its meaning; `PrimOp::name` pairs a source operator with its row. `crates/tatic-wasm/src/machine.rs#Row`, `crates/tatic-wasm/src/machine.rs#Table`, `crates/tatic-wasm/src/machine.rs#Class`, `crates/tatic-wasm/src/wasm.rs#table`
- **Per-instance proof**: a proof that follows one concrete execution; allowed only at arity 0. `crates/tatic/src/proof/per_instance.rs#prove_closure_expr_instance`
- **Peel**: splits a term into parameter count, body and whether it is recursive. `crates/tatic/src/jit/shape.rs#peel`
- **Phase**: a residue class of the stream sequence. `crates/church-bv/src/streams.rs#residue`
- **Plan / LawKind**: the rewriter's proof sketch and the name of the prover of each leaf. `crates/church-bv/src/rewrite/plan.rs#Plan`, `crates/church-bv/src/rewrite/plan.rs#LawKind`
- **Pool**: `POOL=p` hands each mine p x n extras and `EXTRAS_SELECT` keeps n. `crates/church-bv/src/miner/config.rs#ExtrasPlan`
- **Postulates**: the untrusted builder that grows `Globals`; each pushed type is checked to be a type, its inhabitation is assumed. `crates/tatic-kernel/src/postulates.rs#Postulates`
- **PROMOTED**: mined rules frozen in code: learned once, then fixed. `crates/church-bv/src/rewrite/rules.rs#PROMOTED`
- **prove_eq**: the cascade that closes a rewritten pair: refl, truth table, per-position check, mask reduction, join, machine. `crates/church-bv/src/rewrite/join.rs#prove_eq`
- **prove_rule**: proves a rule itself before it is used; the every-input fallback is its last resort. `crates/church-bv/src/rewrite/rules.rs#prove_rule`
- **Rec**: a term form that ties a knot for direct self-recursion. `crates/tatic/src/lang/term.rs#Term`
- **Rule order**: the polynomial weight a rule must lower to be admitted. `crates/church-bv/src/rewrite/rules.rs#rule_order_ok`
- **Sample battery**: the fixed inputs on which compiled code and interpreter must agree. `crates/tatic/src/jit.rs#sample_arg_vectors`
- **Screen**: a random-input test that refutes a claimed law before proving it. `crates/church-bv/src/rewrite/values.rs#SCREEN_INPUTS`
- **Specialisation trace**: the list of beta-v steps replayed by the independent checker. `crates/tatic/src/verify/spec_check.rs#Step`
- **StepProof**: one bit position's step proof over two machines and an encoding, shared by `tree_proof` and the width-free fold. `crates/church-bv/src/machine.rs#StepProof`
- **Stragglers**: laws still needing a machine proof, or not closing, after the base rules. `crates/church-bv/src/miner/laws.rs#laws_of`
- **Straggler-first selection**: with `EXTRAS_SELECT=small` the miner classifies a pool of extras under the mine's base rules and keeps the n stragglers with the fewest rewrite steps, ties (and every straggler of a mine with no mined rules, where steps are all 0) by the smaller normal form; `first` keeps the pool's first n unclassified; `ctx` keeps the same stragglers but orders them by a fitted context model's score instead of by cost (the weights file named by `CTX_WEIGHTS`, columns without the marginal-coverage group). `crates/church-bv/src/miner/laws.rs#kept_indices`
- **Stream / salt**: operator-set law streams, interleaved round-robin; the salt reshuffles. `crates/church-bv/src/streams.rs#stream_sequence`
- **Sweep**: three cold loops for one salt and build. `crates/church-bv/src/driver.rs#run_sweep`
- **TermStore**: the hash-consing store of terms. `crates/tatic/src/lang/term.rs#TermStore`
- **Transfer**: whether rules mined on one set of laws help laws they never saw (the held-out bands). `docs/tier-cycle/#Held-out M and transfer for v0.5`
- **Twin**: an extra whose normalized key equals a served or held-out law's; the extras filter drops it. `docs/tier-cycle/#Metrics`
- **Verdict (gate)**: the installation gate's answer for a term: `Accepted`, `Rejected(Layer, why)` (shape check, walk or kernel) or `NotCovered` (decided from the source alone, then `kernel_verify`). `crates/tatic/src/proof/gate.rs#Verdict`
- **Verdict (kernel to model)**: the per-proposal answer of the cycle's interface: parse error, refuted, trivial, duplicate, known, novel, and cheap or hard. `docs/tier-cycle/#Interface`
- **Wasm model**: wasm-like programs as Church-encoded kernel data and the statement that a function's code simulates its source; separate from the JIT. `crates/tatic-wasm/src/machine.rs#Machine`
- **Work counts**: deterministic counters at four sites, a load-independent cost signal. `crates/church-bv/src/work.rs#Site`
- **Worker**: a persistent child process that runs serve and mine tasks. `crates/church-bv/src/driver.rs#run_worker`

## Where facts live

One home per fact; link instead of restating.
- Goals and open milestones: `ROADMAP.md`. Finished milestones: tag messages.
- Deferred work, with why and trigger: `PARKED.md`.
- Findings and their measurements, organised by topic: `docs/tier-cycle/README.md`. Its sections are cited by name, not line.
- Which pipeline parts are learned or fixed, verdicts only: `docs/learned-vs-fixed.md`.
- Runs: raw output under `%LOCALAPPDATA%\claude-runs\tatic`, one row each in `docs/runs.md` (columns defined by `docs/runs.md#run id`), curated rows in `docs/runs/<date>/`.
- Specs and plans: `docs/superpowers/`, each with a `status:` front matter line that overrides older status text; decisions too long for a parked line go in `docs/decisions/`.
- The type system of the closures fragment: `docs/types.md`. What is proven, and the fuzzers: `docs/proven.md`. The rest of the old README: `docs/syntax.md`, `docs/benchmarks.md`, `docs/design-notes.md`, `docs/loop-experiment.md`.
- Project kind and the rules for all of the above: `CLAUDE.md#tatic`.

## Known doc/code disagreements

Moved to `PARKED.md`, "Stale comments and doc lines found by the tour survey". Two terms are doc measures with no code of their own: the redraw spread and the frontier (the gate computes them from `GEN_DRAW` arms and the held-out bands).
