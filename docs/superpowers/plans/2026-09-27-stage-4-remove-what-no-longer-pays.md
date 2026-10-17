---
status: done
---

# Stage 4: remove what no longer pays — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Delete the workarounds in `src/proof.rs` that existed only because pushed postulates used to shift or go stale. Stage 3 (RELATED_WORK §69, §70) made postulates `Const`s and parameters `Free`s, so these workarounds now do nothing, or only guard a panic.

**Architecture:** Four behaviour-preserving deletions. Each is measured or guarded by existing tests, then removed.
1. `push_ev_facts`, §62's prepass. With `Const`s, a mid-build push shifts nothing, so memo hits share without it. Measure first.
2. `push`'s in-scope panic, plus the closure priming that existed only to avoid it. This also removes the JIT's panic path on a missed prime (§70's failure mode).
3. `Anchored` and `Params`. Both are no-op wrappers now: `at` is `shift(e, 0, 0)` and a copy.

Docs and the A/B come last.

**Tech Stack:** Rust (edition as in `Cargo.toml`), `im::Vector`, cargo test/criterion, `scripts/quiet_ab` for A/B timing.

**Spec:** `docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md`, section "Stage 4: remove what no longer pays". Background in `RELATED_WORK.md`:
- §62 (`push_ev_facts`, one context depth);
- §69 (postulates are `Const`s; push checks);
- §70 (parameters are `Free`s; the push panic and its JIT failure mode);
- §71 (cold-JIT profile: the universal theorem's instances are 34% of cold time; `push_ev_facts` runs inside them).

## Decisions

1. **A push inside an open scope is allowed.** It adds a global, which `close` doesn't wrap. The type must still be closed (no `Var`, no `Free`), and it is still checked to be a type.
   - This is the spec's stage 4 instruction.
   - Cost: a local mistakenly pushed with a closed type (`v : Int`) becomes an extra global instead of panicking.
   - Stage 3b converted every such local to `bind` (45 tests caught them), and a local whose type mentions a parameter still fails, since `push` rejects a `Free`.
2. **`push_ev_facts` is deleted only if measurement agrees.** `fib(16)`'s instance-proof DAG must not grow, and build+check (best of 5) must not get slower by more than 10%. Otherwise keep it and report `DONE_WITH_CONCERNS` with the numbers.
3. **Priming that has become a no-op is deleted.** A priming call that only warms a memo and whose result is discarded goes. A call whose result is used stays. Everything is deleted together with the comment that justified it.
4. **`Anchored` becomes a plain `Expr`, and `Params` a plain slice.** No replacement type.

## Global Constraints

- **Trust boundary:** Stage 4 is untrusted. Do not change the type checker in `src/kernel.rs` (`infer_rc`, `check_rc`, `whnf`, `def_eq`, `shift`, `instantiate`, `check_in`, `infer_in`, the `Const`/`Free` rules). Only these may change there:
  - the `Postulates` section (`pub struct Postulates`, its doc comment and `impl`);
  - kernel tests.
  If a task seems to need a type-checker change, stop and report `BLOCKED`.
- **Line endings:** files are CRLF except `*.sh` (LF).
  - Edit with the Edit tool, or Python with `open(p, encoding='utf-8', newline='')` on both read and write. Always pass `encoding='utf-8'`: the files contain `§` and `µ`, and Windows' default codec corrupts them.
  - Never `sed -i`. Never run `cargo fmt`.
- **Builds:** `CARGO_BUILD_JOBS=12`. Run tests with `cargo test -q --lib` (plus `--release` where a step says so). Timing probes run through `scripts/quiet_ab/pin.sh`.
- **Hands off:**
  - Never touch other sessions' processes: `selfplay*`, `java`/Gradle, `manifold`, League, or other `cargo` jobs.
  - Never touch the worktrees `.claude/worktrees/goofy-sammet-171d91` and `target/bench-ab/base`.
  - Never touch anything under `target/ab*/` (an A/B may be running there).
- **Comments:** match the surrounding density. Cite `RELATED_WORK.md` sections for "why", and state facts plainly.
  - When a deletion makes a comment false (it names `Anchored`, priming, "stale", "cache hit -- primed by", or `push_ev_facts`), delete or restate it in the same task.
  - Don't leave history narration ("used to", "no longer") except one sentence with a § citation where the reason is non-obvious.
- **Commits:** one commit per task, message ending with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Don't push; the controller pushes.
- **Every task ends green:**
  - `cargo test -q --lib` passes;
  - `cargo clippy --all-targets -- -D warnings` is clean;
  - `cargo test --release --test kernel_soundness_fuzz --test compile_fuzz` passes.

## File structure

- `src/proof.rs`: all four removals (~9,600 lines; the builder, provers and tests).
- `src/kernel.rs`: the `Postulates` `push` assertion, its doc comment, and one kernel test (Task 2 only).
- `RELATED_WORK.md`, `README.md`, the spec: docs (Task 4).

---

### Task 1: Measure `push_ev_facts`, then delete it

**Files:**
- Modify: `src/proof.rs`:
  - `canonical_params`'s neighbour `push_ev_facts` (~3567-3604);
  - its call in `instance_from_scaffold` (~3815);
  - the `build_ev_witness` doc comment (~3606-3616), which mentions the prepass indirectly via "fresh as of the moment".
- Test: existing `proof::tests::fib16_instance_proof_cost` (ignored probe, ~9508), and the existing fib DAG tests.

**Interfaces:**
- Consumes: nothing new.
- Produces: `instance_from_scaffold` no longer calls `push_ev_facts`, and `push_ev_facts` no longer exists. `canonical_params`, `trace_leaf` and `WITNESS_NODE_BUDGET` stay, since `build_ev_witness` uses them.

- [ ] **Step 1: Baseline.** Build the release lib tests once, then run the probe 5 times pinned. Record every `dag=`, `build=` and `check=`.

```bash
cargo test --release --lib --no-run
E=$(ls -t target/release/deps/tatic-*.exe | head -1)
for i in 1 2 3 4 5; do scripts/quiet_ab/pin.sh $E fib16_instance_proof_cost --ignored --nocapture 2>&1 | grep "fib16 dag"; done
```

Expected: `dag=10466` (§70), build ~4-9 ms, check ~3-6 ms. If `ls` finds no exe, the release test binary is under `target/release/build/tatic/*/out/`; take the path from `cargo test --release --lib --no-run`'s "Executable" line.

- [ ] **Step 2: Delete the call.** In `instance_from_scaffold`, remove this line and nothing else:

```rust
    push_ev_facts(store, &mut scaffold.combinators, scaffold.self_call, &scaffold.leaves, &concrete, &mut HashSet::new())?;
```

- [ ] **Step 3: Re-measure.** Rebuild, then run the same 5-run loop.
  - `dag` must be ≤ the baseline.
  - Best `build+check` must be ≤ 1.10 × the baseline best.
  - If either fails, restore the line, skip Steps 4-5, and report `DONE_WITH_CONCERNS` with both tables.

- [ ] **Step 4: Delete the function.** Remove `push_ev_facts` (doc comment and body). Then run `cargo build` and fix any "unused" warnings, e.g. a `HashSet` import used only there.
  - In `build_ev_witness`'s doc comment, keep the sentence that says `(v, e)` are returned for the caller to hold.
  - Delete any clause saying the context doesn't grow while the witness is built, or that `Anchored::at` never shifts.
  - Task 3 removes `Anchored` itself, so don't rename it here.

- [ ] **Step 5: Run the gates.**

```bash
cargo test -q --lib
cargo clippy --all-targets -- -D warnings
cargo test --release --test kernel_soundness_fuzz --test compile_fuzz
```

Expected: all pass. `fib16_instance_proof_builds_and_checks_quickly` and the fib DAG comparison test are in the lib suite.

- [ ] **Step 6: Commit.**

```bash
git add src/proof.rs
git commit -m "Stage 4: delete push_ev_facts; memo hits share without it (dag X -> Y, build+check A -> B ms)" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

Fill X, Y, A and B with the measured bests. Put both 5-run tables in the report file.

---

### Task 2: Allow a push inside a scope; delete the closure priming

**Files:**
- Modify: `src/kernel.rs`:
  - `Postulates::push` (~1632): its first `assert!`;
  - the `Postulates` doc comment (~1506-1512);
  - the test `push_panics_inside_a_scope` (~4201-4208).
- Modify: `src/proof.rs`:
  - `prime_closure_postulates` (~1536-1620), `prime_direct_call` (~1632-1650), `prime_closure_if_tree_leaves` (~5801-5840): delete;
  - the two priming loops in `build_universal` (~1927-1982), and the audit comment after them (~1984-2003);
  - every other priming call site (list in Step 5);
  - the `ArithPostulates::lit` doc comment (~226-231), which says `lit` can't be the first push inside a scope.
- Test: new kernel test, replacing `push_panics_inside_a_scope`.

**Interfaces:**
- Consumes: `Postulates::{push, open, bind, close, check, get}`, `Binder::Pi`, and the kernel test helpers `sort`, `pi`, `id`, `var`, `Expr::Const`, all in `src/kernel.rs`'s test module.
- Produces: `Postulates::push` may run while a scope is open. It still asserts a closed type and checks it infers to a `Sort`.

- [ ] **Step 1: Write the failing test.** In `src/kernel.rs`'s test module, replace `push_panics_inside_a_scope` with:

```rust
    /// A push inside a scope adds a global: `close` doesn't wrap it, and
    /// the closed term refers to it by `Const` (RELATED_WORK §70, stage 4).
    #[test]
    fn a_push_inside_a_scope_is_a_global_that_close_leaves_alone() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let s = p.open();
        let x = p.bind(p.get(a));
        let c = p.push(p.get(a));
        let closed = p.close(s, Binder::Pi, id(p.get(a), x, p.get(c)));
        assert_eq!(closed, pi(Expr::Const(0), id(Expr::Const(0), var(0), Expr::Const(1))));
        assert!(p.check(&closed, &sort(0)).is_ok());
        assert_eq!(p.globals.len(), 2);
    }

    #[test]
    #[should_panic(expected = "closed")]
    fn a_push_inside_a_scope_still_rejects_a_parameter_in_its_type() {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let _s = p.open();
        let x = p.bind(p.get(a));
        p.push(id(p.get(a), x.clone(), x));
    }
```

- [ ] **Step 2: Run them.** `cargo test -q --lib a_push_inside_a_scope`

Expected: both FAIL. The first panics with "push while a scope is open". The second panics with the same message, which doesn't contain "closed", because the scope assertion runs before the closedness one. After Step 3, the second passes on `push`'s `free_of == 0` assertion and stays as a guard.

- [ ] **Step 3: Relax `push`.** In `Postulates::push`, delete this line:

```rust
        assert!(self.scopes == 0, "push while a scope is open: bind a scope's entries (RELATED_WORK §70)");
```

In the `Postulates` doc comment, after the `Free`-level paragraph, add:

```rust
///
/// A `push` may happen inside an open scope: it adds a global, which that
/// scope's `close` doesn't wrap. Its type must be closed, so a scope's own
/// entry, whose type mentions a parameter, can't be pushed by mistake;
/// bind it.
```

- [ ] **Step 4: Run the tests.** `cargo test -q --lib`

Expected: all pass. The first new test passes now, and nothing else changes: the priming still runs, it's just no longer needed.

- [ ] **Step 5: Delete the priming.**
  - **Functions:** delete `prime_closure_postulates`, `prime_direct_call` and `prime_closure_if_tree_leaves`, with their doc comments.
  - **Call sites of those functions:** ~1976-1981 (the `for leaf in &leaves` loop in `build_universal`) and ~5053 (`prime_closure_if_tree_leaves(self, &leaf_shapes)?;`).
  - **`clo_ty` loop:** delete `build_universal`'s loop together with its long comment (~1927-1959):

    ```rust
        for k in param_types.iter().flatten() {
            arith.clo_ty(*k);
        }
    ```

    Also delete the audit comment block that follows it (~1984-2003).
  - **Discarded-result calls:** delete every statement whose value is discarded and whose comment says it primes. Known sites:
    - ~5038-5040 (`for lit_n in lits { self.cp.arith.lit(lit_n); }`) and its `collect_closure_if_tree_literals` call above it. Check first: if that call's `false` return rejects the term ("would reject every input outright"), keep the call and its `return None`, and delete only the `for` loop.
    - ~5054 (`self.cp.clo_ty(k); // also primes ...`).
    - ~5050-5052 (`if n_captures > 0 { self.cp.mk_env_ref(&sig); }`) when its result is unused.
    - The same patterns near 5103, 5242, 5255, 5377, 5390, 5431, 5515 and 5603.

    Find them all with:

    ```bash
    python -c "import re;L=open('src/proof.rs',encoding='utf-8').read().split('\n');[print(i+1,l.strip()) for i,l in enumerate(L) if re.search(r'\bprim(e|ed|es|ing)\b',l,re.I)]"
    ```

  - **Keep** a call whose result is bound and used, such as `let call_fn = self.call_ref(...)?;` at ~5048. Only reword its comment if the comment says it primes.
  - **`// cache hit -- primed by X` comments** (~2647, 2836, 2848, 2964, 3132, 3264, 3270, 5852-6040): delete the trailing comment and keep the code.
  - **`ArithPostulates::lit`'s doc comment:** replace the last two sentences with "Scope parameters are `Free`s, and a push inside a scope adds a global, so `lit` may be called at any point."
  - **`prime_closure_postulates`:** if it also validated shapes, a `?` that made `build_universal` return `None` on an unsupported term, then check that `build_universal` still declines those terms. Run the tests that expect `None` from `prove_tail_recursive_universal` (`grep -n "universal(.*).is_none()" src/proof.rs`). If any fails, keep only the validation, renamed `closure_shapes_supported(...) -> Option<()>` with no pushes, and say so in the report.

- [ ] **Step 6: Run the gates.**

```bash
cargo test -q --lib
cargo clippy --all-targets -- -D warnings
cargo test --release --test kernel_soundness_fuzz --test compile_fuzz --test golden_wat
cargo test --release --lib ir_fuzz -- --ignored
```

Expected: all pass. `fib16_instance_proof_cost`'s `dag=` must not grow (run it once and put the line in the report).

- [ ] **Step 7: Check the leftovers.**

```bash
python -c "import re;L=open('src/proof.rs',encoding='utf-8').read().split('\n');print([i+1 for i,l in enumerate(L) if re.search(r'\bprim(e|ed|es|ing)\b',l,re.I)])"
```

Expected: `[]`. If a hit must stay (e.g. a § citation), justify each one in the report.

- [ ] **Step 8: Commit.**

```bash
git add src/kernel.rs src/proof.rs
git commit -m "Stage 4: a push inside a scope adds a global; delete the closure priming" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 3: `Anchored` becomes `Expr`, `Params` becomes `&[Expr]`

**Files:**
- Modify: `src/proof.rs`:
  - `struct Anchored` and its `impl` (~1652-1679), `struct Params` and its `impl` (~1681-1690);
  - `params_and_close` / `params_and_close_typed` (~1692-1760), whose `build` closures take `&Params`;
  - the `push_path` / `push_calls` closures (~1870, ~2014);
  - every use (~191 `Anchored::new`, ~253 `.at(`).
- Test: the existing suite (behaviour-preserving).

**Interfaces:**
- Consumes: nothing new.
- Produces:
  - `params_and_close(arith: &mut ArithPostulates, n, binder, build: impl FnOnce(&mut ArithPostulates, &[Expr]) -> Option<Expr>)`;
  - `params_and_close_typed(combinators: &mut ClosureCombinators<'_>, types, binder, build: impl FnOnce(&mut ClosureCombinators<'_>, &[Expr]) -> Option<Expr>)`.
  - Keep each function's other parameters exactly as they are; only `&Params` becomes `&[Expr]`.
  - Every field or local of type `Anchored` becomes `Expr`, including `UniversalScaffold`'s `combines`, `theorem_ty` and `theorem_proof`, `ValueTriples`, `CloCallBridge`, and the `DynVal` variants.

- [ ] **Step 1: Params by hand.**
  - Delete `struct Params` and its `impl`.
  - In both `params_and_close*`, change `&Params` in the `build` bound to `&[Expr]`. Replace `let pp = Params(params);` with `let pp = params;` and pass `&pp`.
  - At each `pp.at(<anything>)` call site (find with `grep -n "pp.at(" src/proof.rs`), use `pp` directly where a slice works (indexing, `split_at`, `iter`), or `pp.to_vec()` where an owned `Vec<Expr>` is needed.
  - Change `push_path`'s and `push_calls`' `pp: &Params` to `pp: &[Expr]`.
  - Run `cargo build`. Expected: compiles.

- [ ] **Step 2: Anchored by script.** Save as `rewrite_anchored.py` in your scratch directory (not the repo) and run it from the repo root:

```python
import re
p = 'src/proof.rs'
s = open(p, encoding='utf-8', newline='').read()

def rewrite(s, head, repl):
    out, i = [], 0
    while True:
        j = s.find(head, i)
        if j < 0:
            out.append(s[i:]); return ''.join(out)
        out.append(s[i:j])
        k, depth, first_comma = j + len(head), 1, None
        while depth:
            c = s[k]
            if c in '([{': depth += 1
            elif c in ')]}': depth -= 1
            elif c == ',' and depth == 1 and first_comma is None: first_comma = k
            k += 1
        inner = s[j + len(head):k - 1]
        out.append(repl(inner, first_comma - (j + len(head)) if first_comma is not None else None))
        i = k

# Anchored::new(arith, e)  ->  e
s = rewrite(s, 'Anchored::new(', lambda inner, c: inner[c + 1:].strip())
# x.at(arith)  ->  x.clone()
s = rewrite(s, '.at(', lambda inner, c: '.clone()')
open(p, 'w', encoding='utf-8', newline='').write(s)
print(s.count('Anchored::new('), s.count('.at('))
```

Expected output: `0 0`. The `.at(` rewrite runs after Step 1, so every remaining `.at(` is `Anchored::at`. Check first with `grep -c "\.at(" src/proof.rs`: every hit should be on an `Anchored` value. If one isn't, rename it before running the script, and say so in the report.

- [ ] **Step 3: Replace the type.**
  - Delete `struct Anchored`, its doc comment and its `impl`.
  - Replace the remaining type uses of `Anchored` (field types, `Vec<Anchored>`, tuple types, `DynVal`'s variants, function signatures) with `Expr`.
  - Run `cargo build`, then fix the errors it reports. They'll be moved-value errors where the old `.at()` produced a fresh value: add `.clone()`. Or double `.clone().clone()`: collapse it.
  - Then run `cargo clippy --all-targets -- -D warnings`, and fix `redundant_clone` / `clone_on_copy` hits by dropping the clone.

- [ ] **Step 4: Comments.** Delete or restate every comment that mentions `Anchored` or staleness.

```bash
grep -n "Anchored\|stale" src/proof.rs
```

- Expected: no `Anchored`.
- For each `stale` hit, keep it only if it describes history in one sentence with a § citation. Otherwise delete it.
- Comments like "Anchored *before* computing `clo_ty(arity - k)`" and "same staleness class" describe an ordering that no longer matters. Delete them.

- [ ] **Step 5: Run the gates.**

```bash
cargo test -q --lib
cargo clippy --all-targets -- -D warnings
cargo test --release --test kernel_soundness_fuzz --test compile_fuzz --test golden_wat
cargo test --release --lib ir_fuzz -- --ignored
```

Expected: all pass. Run `fib16_instance_proof_cost` once and put its line in the report. `dag=` must not change from Task 2's value.

- [ ] **Step 6: Commit.**

```bash
git add src/proof.rs
git commit -m "Stage 4: Anchored becomes Expr and Params a slice; both were no-ops since stage 3" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

### Task 4: Docs

**Files:**
- Modify:
  - `RELATED_WORK.md`: new `## 72. Stage 4: what stage 3 made unnecessary`, before `## Sources`;
  - `README.md` (~1114-1122, the stage 3/stage 4 sentence);
  - the spec's status line (line 3-5) and its "Stage 4" section (~296-313).

- [ ] **Step 1: Write §72.** 15-30 lines, in §69/§70's style (bold lead-ins: **What was removed.**, **Measured.**, **What changed in behaviour.**). Include:
  - Task 1's DAG and build/check before and after (from its report), or why `push_ev_facts` stayed.
  - The number of priming functions, loops and call sites deleted in Task 2. Say that §70's JIT panic path is gone, because no push can panic for being inside a scope.
  - Decision 1's cost, stated plainly: a closed-typed local pushed by mistake becomes an extra global.
  - `Anchored` and `Params` removed; the `proof.rs` line count before and after (`wc -l src/proof.rs` at the plan's base commit and now).
  - "A/B pending: <base> vs <head>, `target/ab4`". The controller fills in the costs.

- [ ] **Step 2: README.** Replace "Stage 4, removing the workarounds this makes unnecessary, is designed but not built." with one sentence saying stage 4 is built (§72) and what it removed.

- [ ] **Step 3: Spec.**
  - Status line: "stage 4 built (§72)".
  - Under "Stage 4", add a short "Built:" paragraph listing any departure from its bullets. For example, whether `push_ev_facts` was kept, and that the push-check prelude cost is handled by `ArithPostulates::new`'s thread-local prelude (commit 7e6d61c).

- [ ] **Step 4: Commit.**

```bash
git add RELATED_WORK.md README.md docs/superpowers/specs/2026-09-25-kernel-constants-and-loose-ranges-design.md
git commit -m "Docs: RELATED_WORK §72 (stage 4), README and spec status" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
```

---

## After the plan (controller)

- Run the A/B: plan base vs Task 3's head, fib16 probe (10 pairs) and proof benches (5 pairs), in `target/ab4`, via `scripts/quiet_ab/ab.sh`. Fill in §72's cost.
- Include the JIT execution bench's `jit_cold_compile_and_verify` rows if Task 1 deleted `push_ev_facts`, since that code ran inside the cold JIT's instance step (§71).
