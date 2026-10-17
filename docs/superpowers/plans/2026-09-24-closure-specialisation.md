---
status: done
---

# Closure specialisation (certificate-checked βv): implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Inline closures known at compile time by rewriting the source term
with βv steps. Every rewrite is replayed and checked by an independent
checker before the JIT compiles the result.

**Architecture:**
- **`src/spec_check.rs`** (trusted) defines the certificate `Step` and
  `check`. `check` replays a trace from `h` using its own substitution and
  accepts only if the replay ends at the claimed hash.
- **`src/specialise.rs`** (untrusted) produces `(store, h', trace)` under
  the spine policy.
- **`compile::compile_specialised`** is the one pipeline driver: specialise,
  then check, then `try_compile` on the chosen term. `try_compile` itself is
  unchanged.
- **`jit.rs`** calls the driver. It verifies against the original `h` and
  runs `kernel_verify` on the term it actually compiled.

**Tech Stack:** Rust 2024, wasmtime 42, blake3 content hashes.

**Spec:** `docs/superpowers/specs/2026-09-24-closure-specialisation-design.md`.
Read all of it before starting. The sections that matter most are
"Semantics this must respect", "Architecture" and "Specialiser policy".

## Global Constraints

- **Toolchain.** Before any `cargo` command:
  `export PATH="/c/Users/Winston Li/scoop/persist/rustup/.cargo/bin:$PATH"`.
  The shell is Git Bash on Windows.
- **Line endings.** Source files are CRLF in the working tree
  (`core.autocrlf=true`). Edit existing files with the Edit tool only; no
  `sed -i`. New files may be LF.
- **Existing WAT unchanged.** The 25 existing files in `tests/golden/` must
  not change; `git diff --stat -- tests/golden` shows no modified files.
  Task 3 adds exactly two new ones, `*_specialised.wat`.
- **`try_compile` unchanged.** Its body and contract stay as they are. Only
  the new driver specialises.
- **Checker independence.** `src/spec_check.rs` may use only `crate::term`
  and `std`, with both `crate::` and `super::` paths scanned; a test
  enforces this. `src/specialise.rs` may use `crate::spec_check` only for
  `Step`, `MAX_STEPS` and `MAX_NODES`, and must not call `check` or any of
  the checker's substitution code. The specialiser has its own
  substitution.
- **Limits.** `MAX_STEPS = 256`, `MAX_NODES = 4096`, defined in
  `spec_check.rs`.
- **Counter.** `compile::spec_check_failures()` is process-wide. Only
  `tests/compile_fuzz.rs`, which runs in its own process, asserts it is 0.
  No lib test asserts it, because a `should_panic` lib test increments it
  on purpose.
- **Full validation after every task.** Every step must pass; expected
  values are in brackets.
  1. `cargo build --all-targets` [0 errors]
  2. `cargo test --lib --bins` [all pass; 229 passed, 1 ignored before Task 1; check the delta]
  3. `cargo clippy --all-targets` [no new warnings; the `term.rs` `entity_impl!` warning is pre-existing]
  4. `cargo test --release --test compile_fuzz --test kernel_fuzz --test kernel_soundness_fuzz --test syntax_fuzz` [5+2+3+1 pass; compile_fuzz becomes 6 in Task 4]
  5. `cargo test --test golden_wat` [1 pass; 2 from Task 3]
  6. `cargo run --release 2>&1 | grep "JIT stats"` [`compiled: 9, ... declined_no_universal_proof: 0` before Task 3; from Task 3 on, record the new line and explain any change]
  7. `cargo bench --bench execution -- --warm-up-time 0.3 --measurement-time 0.5 --sample-size 10` [21 bars, no panics]
  8. `cargo bench --bench proofs -- --warm-up-time 0.3 --measurement-time 0.5 --sample-size 10` [17 bars, no panics]
  9. `cargo test --release --lib ir_fuzz -- --ignored` [pass]

  Run long commands in the **foreground** with a long timeout and grep
  their output. Background jobs are lost when a subagent's turn ends. Never
  read a whole log into context.
- **Verify-teeth.** Break every new check on purpose, confirm it fails,
  then revert. Each task lists the breaks it needs.
- **Commit and push after each task.** The branch is
  `claude/closure-specialisation`. End each commit message with your
  harness's Co-Authored-By line.
- **Style.** Doc comments explain *why*. No speculative abstraction and no
  new dependencies. Use `std::collections` in the new modules.

---

### Task 1: The checker and the shared independence scan

**Files:**
- Create: `src/spec_check.rs`, `src/independence.rs`
- Modify: `src/lib.rs`, `src/decompile.rs` (its independence test only)

**Interfaces:**
- Consumes: `term::{Hash, Term, TermStore}`.
- Produces:
  - `spec_check::{Step, CheckError, check, MAX_STEPS, MAX_NODES}`:
    ```rust
    pub enum Step { BetaV { redex: Hash } }                    // Clone, Copy, Debug, PartialEq, Eq
    pub struct CheckError { pub step: usize, pub reason: &'static str }  // Clone, Copy, Debug, PartialEq, Eq
    pub fn check(store: &TermStore, h: Hash, trace: &[Step], claimed: Hash) -> Result<(), CheckError>
    ```
  - `independence::assert_independent(file: &str, src: &str, forbidden: &[&str], allowed: &[&str])`
    (test-only).

- [ ] **Step 1: Register the modules.** In `src/lib.rs`, add
  `pub mod spec_check;` after `pub mod proof;`, and add
  `#[cfg(test)] mod independence;` next to `#[cfg(test)] mod ir_fuzz;`.

- [ ] **Step 2: Move the independence scan into `src/independence.rs`.**
  Create the file below. Its body is the scan from `decompile.rs`'s
  `the_decompiler_imports_nothing_from_the_compiler`, parameterised by file
  name, forbidden tokens and allowed module heads.

```rust
//! Test-only: the decompiler and the specialisation checker are trusted
//! only because they share no code with what they check. This enforces
//! that mechanically, over the code above a file's `#[cfg(test)] mod tests`
//! (the tests may use anything).

/// Panics if `src` (the contents of `file`), above its test module and
/// ignoring `//` comments:
/// - contains any token in `forbidden`. The check is token by token, so
///   `use crate :: compile :: peel;` or `use crate::{compile::peel};`
///   can't slip past a substring match.
/// - uses `super::super`.
/// - has a `crate::` or `super::` path whose first segment is not in
///   `allowed`. Both prefixes are scanned because a module directly under
///   the crate root reaches the same siblings through `super::` as through
///   `crate::`. `crate::{..}` has an empty first segment and is rejected
///   too.
pub(crate) fn assert_independent(file: &str, src: &str, forbidden: &[&str], allowed: &[&str]) {
    let lines: Vec<&str> = src.lines().collect();
    let tests_start = lines
        .iter()
        .enumerate()
        .find(|(i, l)| l.trim() == "#[cfg(test)]" && lines.get(i + 1).is_some_and(|next| next.trim_start().starts_with("mod tests")))
        .map_or(lines.len(), |(i, _)| i);
    let code: Vec<&str> = lines[..tests_start].iter().map(|l| l.trim_start()).filter(|l| !l.starts_with("//")).collect();
    for tok in forbidden {
        let hit = code.iter().any(|l| l.split(|c: char| !c.is_alphanumeric() && c != '_').any(|t| t == *tok));
        assert!(!hit, "{file} must not use {tok}");
    }
    assert!(!code.iter().any(|l| l.contains("use super::super")), "{file} must not use super::super");
    for l in &code {
        // Collapse whitespace so `crate :: compile` can't dodge the
        // `crate::` search. `pub(crate)` has no `::` after `crate`, so it
        // never matches.
        let compact: String = l.chars().filter(|c| !c.is_whitespace()).collect();
        for prefix in ["crate::", "super::"] {
            let mut rest = compact.as_str();
            while let Some(i) = rest.find(prefix) {
                let after = &rest[i + prefix.len()..];
                let end = after.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(after.len());
                let head = &after[..end];
                assert!(allowed.contains(&head), "{file} must not use {prefix}{head} (only {allowed:?} are allowed)");
                rest = &after[end..];
            }
        }
    }
}
```

  Replace the body of `decompile.rs`'s
  `the_decompiler_imports_nothing_from_the_compiler`. Keep its leading
  comment explaining why, and trim the comment's mechanics that now live in
  the helper. The new body is:

```rust
        crate::independence::assert_independent("decompile.rs", include_str!("decompile.rs"), &["compile", "lower_wat"], &["ir", "term"]);
```

  Run `cargo test --lib the_decompiler_imports_nothing` [pass]. Teeth:
  temporarily add `use super::proof;` above `decompile.rs`'s test module.
  The test must fail with "decompile.rs must not use super::proof". Revert.

- [ ] **Step 3: Write `src/spec_check.rs`, with an empty test module to
  start.**

```rust
//! The trusted half of closure specialisation. It replays a certificate (a
//! trace of βv steps) from the source term, and accepts only if every step
//! is a real βv contraction and the replay ends at exactly the claimed
//! term. See `docs/superpowers/specs/2026-09-24-closure-specialisation-design.md`.
//!
//! Why βv and nothing more: `eval` is call-by-value, with errors
//! (`DivByZero`, `TypeError`, ...) and unbounded `Rec`, so full β is
//! unsound (`(\x. 0) (1/0)` fails; `0` doesn't). For a value `V` (`Var`,
//! `Lit`, `Abs`, `Rec`), `(\. M) V = M[0 := V]` is an observational
//! equivalence closed under every context (Plotkin 1975). So a step may
//! rewrite anywhere, including under binders. Because an equal subterm
//! may be replaced in any context, a step also rewrites every occurrence
//! at once. `App(Rec, V)` is never a redex: `Rec` is never unfolded.
//!
//! This file is independent of the specialiser by construction. It uses
//! only `crate::term` and `std` (a test enforces this) and has its own
//! substitution, so a bug in `specialise.rs`'s substitution cannot be
//! mirrored here.

use crate::term::{Hash, Term, TermStore};
use std::collections::{HashMap, HashSet};

/// The longest trace `check` accepts. The specialiser stops here too.
pub const MAX_STEPS: usize = 256;
/// The most distinct nodes any term in a replay may have. The specialiser
/// stops here too.
pub const MAX_NODES: usize = 4096;

/// One certificate step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step {
    /// Contract the βv redex `redex`, an `App(Abs(body), value)`, to
    /// `body[0 := value]`. Every occurrence in the current term is
    /// rewritten in one pass; occurrences the contraction itself creates
    /// are not rewritten.
    BetaV { redex: Hash },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckError {
    /// The index of the failing step, or `trace.len()` for a failure after
    /// the last step.
    pub step: usize,
    pub reason: &'static str,
}

/// Accepts iff replaying `trace` from `h` (resolved in `store`) is valid at
/// every step and ends at `claimed`.
pub fn check(store: &TermStore, h: Hash, trace: &[Step], claimed: Hash) -> Result<(), CheckError> {
    let fail = |step, reason| Err(CheckError { step, reason });
    if trace.len() > MAX_STEPS {
        return fail(trace.len(), "trace longer than MAX_STEPS");
    }
    if node_count(store, h) > MAX_NODES {
        return fail(0, "source term larger than MAX_NODES");
    }
    let mut s = TermStore::new();
    let mut cur = copy(store, &mut s, h, &mut HashMap::new());
    for (i, step) in trace.iter().enumerate() {
        let Step::BetaV { redex } = *step;
        if !occurs(&s, cur, redex) {
            return fail(i, "redex does not occur in the current term");
        }
        let &Term::App(f, a) = s.resolve(redex) else {
            return fail(i, "redex is not an application");
        };
        let &Term::Abs(body) = s.resolve(f) else {
            return fail(i, "redex head is not a lambda");
        };
        if !matches!(s.resolve(a), Term::Var(_) | Term::Lit(_) | Term::Abs(_) | Term::Rec(_)) {
            return fail(i, "redex argument is not a value");
        }
        let contracted = beta(&mut s, body, a);
        cur = replace_all(&mut s, cur, redex, contracted, &mut HashMap::new());
        if node_count(&s, cur) > MAX_NODES {
            return fail(i, "term larger than MAX_NODES");
        }
    }
    if cur != claimed {
        return fail(trace.len(), "replay does not end at the claimed term");
    }
    Ok(())
}

fn children(t: &Term) -> Vec<Hash> {
    match *t {
        Term::Var(_) | Term::Lit(_) => vec![],
        Term::Prim(_, a, b) | Term::App(a, b) => vec![a, b],
        Term::If(c, x, y) => vec![c, x, y],
        Term::Abs(b) | Term::Rec(b) => vec![b],
    }
}

/// Distinct nodes reachable from `h`. It stops counting once past
/// `MAX_NODES`, since callers only compare against that.
fn node_count(s: &TermStore, h: Hash) -> usize {
    let mut seen = HashSet::new();
    let mut stack = vec![h];
    while let Some(t) = stack.pop() {
        if seen.insert(t) {
            if seen.len() > MAX_NODES {
                break;
            }
            stack.extend(children(s.resolve(t)));
        }
    }
    seen.len()
}

fn occurs(s: &TermStore, t: Hash, target: Hash) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![t];
    while let Some(u) = stack.pop() {
        if u == target {
            return true;
        }
        if seen.insert(u) {
            stack.extend(children(s.resolve(u)));
        }
    }
    false
}

/// Rebuilds `t` with `f` applied to each child. `f` also receives how many
/// binders the child sits under relative to `t`: 1 for an `Abs`/`Rec`
/// body, 0 otherwise.
fn rebuild(s: &mut TermStore, t: Term, mut f: impl FnMut(&mut TermStore, Hash, u32) -> Hash) -> Hash {
    let t = match t {
        Term::Var(_) | Term::Lit(_) => t,
        Term::Prim(op, a, b) => {
            let a = f(s, a, 0);
            Term::Prim(op, a, f(s, b, 0))
        }
        Term::If(c, x, y) => {
            let c = f(s, c, 0);
            let x = f(s, x, 0);
            Term::If(c, x, f(s, y, 0))
        }
        Term::Abs(b) => Term::Abs(f(s, b, 1)),
        Term::App(g, a) => {
            let g = f(s, g, 0);
            Term::App(g, f(s, a, 0))
        }
        Term::Rec(b) => Term::Rec(f(s, b, 1)),
    };
    s.intern(t)
}

/// Copies `h` and everything it reaches into `to`. Hashes are content
/// hashes, so every node keeps its hash.
fn copy(from: &TermStore, to: &mut TermStore, h: Hash, memo: &mut HashMap<Hash, Hash>) -> Hash {
    if let Some(&c) = memo.get(&h) {
        return c;
    }
    let c = rebuild(to, from.resolve(h).clone(), |to, child, _| copy(from, to, child, memo));
    memo.insert(h, c);
    c
}

/// Adds `d` to every variable of `t` with index `>= cutoff`, i.e. every
/// variable free relative to `cutoff` enclosing binders.
fn shift(s: &mut TermStore, t: Hash, cutoff: u32, d: i64, memo: &mut HashMap<(Hash, u32), Hash>) -> Hash {
    if let Some(&r) = memo.get(&(t, cutoff)) {
        return r;
    }
    let term = s.resolve(t).clone();
    let r = match term {
        Term::Var(i) if i >= cutoff => {
            let j = u32::try_from(i64::from(i) + d).expect("a downward shift reached a negative index, so beta left the substituted variable behind");
            s.var(j)
        }
        other => rebuild(s, other, |s, c, bind| shift(s, c, cutoff + bind, d, memo)),
    };
    memo.insert((t, cutoff), r);
    r
}

/// `t[j := v shifted up by j]` (TAPL's `[j ↦ s]t`, with the shift of `s`
/// applied lazily at each hit and cached per depth in `v_at`).
fn subst(s: &mut TermStore, t: Hash, j: u32, v: Hash, memo: &mut HashMap<(Hash, u32), Hash>, v_at: &mut HashMap<u32, Hash>) -> Hash {
    if let Some(&r) = memo.get(&(t, j)) {
        return r;
    }
    let term = s.resolve(t).clone();
    let r = match term {
        Term::Var(i) if i == j => match v_at.get(&j) {
            Some(&r) => r,
            None => {
                let r = shift(s, v, 0, i64::from(j), &mut HashMap::new());
                v_at.insert(j, r);
                r
            }
        },
        other => rebuild(s, other, |s, c, bind| subst(s, c, j + bind, v, memo, v_at)),
    };
    memo.insert((t, j), r);
    r
}

/// The βv contraction of `App(Abs(body), a)`:
/// `↑⁻¹([0 ↦ ↑¹a] body)` (Pierce, TAPL §6.3).
fn beta(s: &mut TermStore, body: Hash, a: Hash) -> Hash {
    let a_up = shift(s, a, 0, 1, &mut HashMap::new());
    let substituted = subst(s, body, 0, a_up, &mut HashMap::new(), &mut HashMap::new());
    shift(s, substituted, 0, -1, &mut HashMap::new())
}

/// `t` with every occurrence of `target` replaced by `with`, in one pass.
/// The replacement is context-free: an equal subterm has the same free
/// variables wherever it occurs.
fn replace_all(s: &mut TermStore, t: Hash, target: Hash, with: Hash, memo: &mut HashMap<Hash, Hash>) -> Hash {
    if t == target {
        return with;
    }
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let term = s.resolve(t).clone();
    let r = rebuild(s, term, |s, c, _| replace_all(s, c, target, with, memo));
    memo.insert(t, r);
    r
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::PrimOp;
}
```

  Run `cargo build` [0 errors]. If the borrow checker rejects a
  `let &Term::App(f, a) = s.resolve(redex)` pattern, bind the resolved term
  first (`let t = s.resolve(redex).clone();`), then match on `t`.

- [ ] **Step 4: Write the checker's unit tests** in `spec_check.rs`'s test
  module.

```rust
    fn one_step(s: &TermStore, h: Hash, redex: Hash, claimed: Hash) -> Result<(), CheckError> {
        check(s, h, &[Step::BetaV { redex }], claimed)
    }

    #[test]
    fn accepts_beta_v_with_a_literal_argument() {
        // (\x. x + 1) 5  ->  5 + 1
        let mut s = TermStore::new();
        let (x, one, five) = (s.var(0), s.lit(1), s.lit(5));
        let body = s.prim(PrimOp::Add, x, one);
        let lam = s.abs(body);
        let r = s.app(lam, five);
        let want = s.prim(PrimOp::Add, five, one);
        assert_eq!(one_step(&s, r, r, want), Ok(()));
    }

    #[test]
    fn accepts_beta_v_with_a_free_variable_argument() {
        // At top level, Var(3) is free: (\x. x + 1) v3  ->  v3 + 1.
        let mut s = TermStore::new();
        let (x, one, v3) = (s.var(0), s.lit(1), s.var(3));
        let body = s.prim(PrimOp::Add, x, one);
        let lam = s.abs(body);
        let r = s.app(lam, v3);
        let want = s.prim(PrimOp::Add, v3, one);
        assert_eq!(one_step(&s, r, r, want), Ok(()));
    }

    #[test]
    fn accepts_a_capturing_lambda_substituted_under_a_binder() {
        // (\g. \z. g z) (\y. y + v1)  ->  \z. (\y. y + v3) z
        // v1 is free at top level. Under the new \z and the \y, it is Var(3).
        let mut s = TermStore::new();
        let (v0, v1, v2, v3) = (s.var(0), s.var(1), s.var(2), s.var(3));
        let gz = s.app(v1, v0);
        let inner = s.abs(gz);
        let caller = s.abs(inner);
        let arg_body = s.prim(PrimOp::Add, v0, v2);
        let arg = s.abs(arg_body);
        let r = s.app(caller, arg);
        let want_arg_body = s.prim(PrimOp::Add, v0, v3);
        let want_arg = s.abs(want_arg_body);
        let want_app = s.app(want_arg, v0);
        let want = s.abs(want_app);
        assert_eq!(one_step(&s, r, r, want), Ok(()));
    }

    #[test]
    fn accepts_a_substitution_into_a_rec_body() {
        // (\x. rec f n. n + x) 7  ->  rec f n. n + 7
        // Inside the Rec's Abs, Var(0) = n, Var(1) = f and Var(2) = x.
        let mut s = TermStore::new();
        let (v0, v2, seven) = (s.var(0), s.var(2), s.lit(7));
        let add = s.prim(PrimOp::Add, v0, v2);
        let abs = s.abs(add);
        let rec = s.rec(abs);
        let lam = s.abs(rec);
        let r = s.app(lam, seven);
        let want_add = s.prim(PrimOp::Add, v0, seven);
        let want_abs = s.abs(want_add);
        let want = s.rec(want_abs);
        assert_eq!(one_step(&s, r, r, want), Ok(()));
    }

    #[test]
    fn accepts_a_rec_and_a_lambda_as_values() {
        // (\x. x) V  ->  V, for V = \y. y and V = rec f n. n.
        let mut s = TermStore::new();
        let v0 = s.var(0);
        let id = s.abs(v0);
        let rec_abs = s.abs(v0);
        let rec = s.rec(rec_abs);
        for v in [id, rec] {
            let r = s.app(id, v);
            assert_eq!(one_step(&s, r, r, v), Ok(()));
        }
    }

    #[test]
    fn rewrites_every_occurrence_in_one_step() {
        // R + R, where R = (\x. x) 1  ->  1 + 1
        let mut s = TermStore::new();
        let (v0, one) = (s.var(0), s.lit(1));
        let id = s.abs(v0);
        let r = s.app(id, one);
        let t = s.prim(PrimOp::Add, r, r);
        let want = s.prim(PrimOp::Add, one, one);
        assert_eq!(one_step(&s, t, r, want), Ok(()));
    }

    #[test]
    fn an_empty_trace_accepts_only_the_source_term() {
        let mut s = TermStore::new();
        let (one, two) = (s.lit(1), s.lit(2));
        assert_eq!(check(&s, one, &[], one), Ok(()));
        assert_eq!(check(&s, one, &[], two).unwrap_err().reason, "replay does not end at the claimed term");
    }

    #[test]
    fn rejects_a_non_value_argument() {
        // (\x. 0) A for A an App, a Prim and an If: none are values.
        let mut s = TermStore::new();
        let (v0, zero, one) = (s.var(0), s.lit(0), s.lit(1));
        let k0 = s.abs(zero);
        let id = s.abs(v0);
        let app = s.app(id, one);
        let div = s.prim(PrimOp::Div, one, zero);
        let iff = s.if_(one, one, zero);
        for a in [app, div, iff] {
            let r = s.app(k0, a);
            assert_eq!(one_step(&s, r, r, zero).unwrap_err().reason, "redex argument is not a value");
        }
    }

    #[test]
    fn rejects_a_rec_in_head_position() {
        let mut s = TermStore::new();
        let (v0, one) = (s.var(0), s.lit(1));
        let abs = s.abs(v0);
        let rec = s.rec(abs);
        let r = s.app(rec, one);
        assert_eq!(one_step(&s, r, r, one).unwrap_err().reason, "redex head is not a lambda");
    }

    #[test]
    fn rejects_a_redex_that_does_not_occur() {
        let mut s = TermStore::new();
        let (v0, one, two) = (s.var(0), s.lit(1), s.lit(2));
        let id = s.abs(v0);
        let elsewhere = s.app(id, one);
        assert_eq!(one_step(&s, two, elsewhere, one).unwrap_err().reason, "redex does not occur in the current term");
    }

    #[test]
    fn rejects_a_correct_replay_with_the_wrong_claim() {
        let mut s = TermStore::new();
        let (v0, one, two) = (s.var(0), s.lit(1), s.lit(2));
        let id = s.abs(v0);
        let r = s.app(id, one);
        let err = one_step(&s, r, r, two).unwrap_err();
        assert_eq!((err.step, err.reason), (1, "replay does not end at the claimed term"));
    }

    #[test]
    fn rejects_traces_and_terms_over_the_limits() {
        let mut s = TermStore::new();
        let (v0, one) = (s.var(0), s.lit(1));
        let id = s.abs(v0);
        let r = s.app(id, one);
        let long = vec![Step::BetaV { redex: r }; MAX_STEPS + 1];
        assert_eq!(check(&s, r, &long, one).unwrap_err().reason, "trace longer than MAX_STEPS");
        // A chain of MAX_NODES distinct Adds has more than MAX_NODES nodes.
        let mut big = one;
        for i in 0..MAX_NODES as i64 {
            let lit = s.lit(i + 2);
            big = s.prim(PrimOp::Add, big, lit);
        }
        assert_eq!(check(&s, big, &[], big).unwrap_err().reason, "source term larger than MAX_NODES");
    }

    #[test]
    fn the_checker_imports_nothing_but_term() {
        crate::independence::assert_independent("spec_check.rs", include_str!("spec_check.rs"), &["specialise", "compile", "lower_wat"], &["term"]);
    }
```

  Run `cargo test --lib spec_check` [13 pass].

- [ ] **Step 5: Teeth.** Apply each break below, confirm the listed test
  fails, then revert.
  - Allow `Term::App(..)` in the value `matches!`:
    `rejects_a_non_value_argument` fails.
  - Change `cutoff + bind` to `cutoff` in `shift`'s `rebuild` closure:
    `accepts_a_capturing_lambda_substituted_under_a_binder` fails.
  - Replace the final `if cur != claimed` block with nothing:
    `rejects_a_correct_replay_with_the_wrong_claim` and
    `an_empty_trace_accepts_only_the_source_term` fail.
  - Add `use super::jit;` above the test module:
    `the_checker_imports_nothing_but_term` fails.

- [ ] **Step 6: Full validation** (checks 1-9). Lib+bins goes up by 13.
- [ ] **Step 7: Commit and push.** Message: "Add the specialisation
  certificate checker and share the independence scan".

---

### Task 2: The specialiser

**Files:**
- Create: `src/specialise.rs`
- Modify: `src/lib.rs`

**Interfaces:**
- Consumes: `spec_check::{Step, MAX_STEPS, MAX_NODES}` and, in tests only,
  `spec_check::check`; `term::*`; `test_corpus::terms()` (tests).
- Produces:
  ```rust
  pub struct Specialised { pub store: TermStore, pub term: Hash, pub trace: Vec<Step> }
  pub fn specialise(store: &TermStore, h: Hash) -> Specialised
  ```
  `term == h` and `trace` is empty when nothing reduces.

- [ ] **Step 1: Register** `pub mod specialise;` after `pub mod spec_check;`
  in `src/lib.rs`.

- [ ] **Step 2: Write `src/specialise.rs`.** It uses its own substitution,
  a single-pass instantiate, which is deliberately a different algorithm
  from the checker's three-pass TAPL `beta`.

```rust
//! The untrusted half of closure specialisation. It rewrites a term by βv
//! steps that inline known closures, and records each step so
//! `spec_check::check` can replay it. Nothing here has to be right for the
//! result to be sound: a wrong step is rejected by the checker, which uses
//! its own substitution. It only has to be right for the result to be
//! fast. The policy is in the spec's "Specialiser policy"
//! (`docs/superpowers/specs/2026-09-24-closure-specialisation-design.md`).

use crate::spec_check::{MAX_NODES, MAX_STEPS, Step};
use crate::term::{Hash, Term, TermStore};
use std::collections::{HashMap, HashSet};

pub struct Specialised {
    /// Holds `term` and everything it reaches. Hashes are content hashes,
    /// so `h`'s own subterms keep their hashes here.
    pub store: TermStore,
    pub term: Hash,
    pub trace: Vec<Step>,
}

/// Reduces, innermost first, every application spine the policy allows,
/// until none is left or a limit (`MAX_STEPS`, `MAX_NODES`) is reached.
/// Any prefix of a valid trace is itself valid, so stopping early is safe.
pub fn specialise(store: &TermStore, h: Hash) -> Specialised {
    let mut s = TermStore::new();
    let mut cur = import(store, &mut s, h, &mut HashMap::new());
    let mut trace = Vec::new();
    'spines: while let Some(spine) = find_spine(&s, cur) {
        let (mut head, mut args) = unwind(&s, spine);
        let k = count_abs(&s, head).min(args.len());
        for i in 0..k {
            if trace.len() == MAX_STEPS {
                break 'spines;
            }
            let redex = s.app(head, args[i]);
            let Term::Abs(body) = s.resolve(head).clone() else {
                unreachable!("the first k heads of a reducible spine are lambdas");
            };
            let contracted = instantiate(&mut s, body, args[i]);
            let next = replace(&mut s, cur, redex, contracted, &mut HashMap::new());
            if size(&s, next) > MAX_NODES {
                break 'spines;
            }
            trace.push(Step::BetaV { redex });
            cur = next;
            head = contracted;
            // The pass rewrote every occurrence of `redex`, including any
            // inside the spine's remaining arguments. Track that, so the
            // next redex is the one actually in `cur`.
            let mut memo = HashMap::new();
            for a in &mut args[i + 1..] {
                *a = replace(&mut s, *a, redex, contracted, &mut memo);
            }
        }
    }
    Specialised { store: s, term: cur, trace }
}

fn import(from: &TermStore, to: &mut TermStore, h: Hash, memo: &mut HashMap<Hash, Hash>) -> Hash {
    if let Some(&c) = memo.get(&h) {
        return c;
    }
    let c = match from.resolve(h).clone() {
        t @ (Term::Var(_) | Term::Lit(_)) => to.intern(t),
        Term::Prim(op, a, b) => {
            let (a, b) = (import(from, to, a, memo), import(from, to, b, memo));
            to.prim(op, a, b)
        }
        Term::If(c, x, y) => {
            let (c, x, y) = (import(from, to, c, memo), import(from, to, x, memo), import(from, to, y, memo));
            to.if_(c, x, y)
        }
        Term::Abs(b) => {
            let b = import(from, to, b, memo);
            to.abs(b)
        }
        Term::App(f, a) => {
            let (f, a) = (import(from, to, f, memo), import(from, to, a, memo));
            to.app(f, a)
        }
        Term::Rec(b) => {
            let b = import(from, to, b, memo);
            to.rec(b)
        }
    };
    memo.insert(h, c);
    c
}

/// `t` as `(head, [a₁, .., a_n])` for `t = App(…App(head, a₁)…, a_n)`.
fn unwind(s: &TermStore, mut t: Hash) -> (Hash, Vec<Hash>) {
    let mut args = Vec::new();
    while let &Term::App(f, a) = s.resolve(t) {
        args.push(a);
        t = f;
    }
    args.reverse();
    (t, args)
}

/// How many `Abs` binders `t` starts with (a `Rec` does not count).
fn count_abs(s: &TermStore, mut t: Hash) -> usize {
    let mut n = 0;
    while let &Term::Abs(b) = s.resolve(t) {
        n += 1;
        t = b;
    }
    n
}

/// `t` with its first `k` `Abs` binders removed.
fn peel(s: &TermStore, mut t: Hash, k: usize) -> Hash {
    for _ in 0..k {
        let &Term::Abs(b) = s.resolve(t) else { unreachable!("peel past the leading lambdas") };
        t = b;
    }
    t
}

/// The first reducible maximal spine, visiting arguments before the spine
/// that takes them. So when a spine is judged, its arguments have already
/// been reduced as far as they can be.
fn find_spine(s: &TermStore, t: Hash) -> Option<Hash> {
    fn go(s: &TermStore, t: Hash, in_fn_pos: bool, seen: &mut HashSet<(Hash, bool)>) -> Option<Hash> {
        if !seen.insert((t, in_fn_pos)) {
            return None;
        }
        match *s.resolve(t) {
            Term::Var(_) | Term::Lit(_) => None,
            Term::Prim(_, a, b) => go(s, a, false, seen).or_else(|| go(s, b, false, seen)),
            Term::If(c, x, y) => go(s, c, false, seen).or_else(|| go(s, x, false, seen)).or_else(|| go(s, y, false, seen)),
            Term::Abs(b) | Term::Rec(b) => go(s, b, false, seen),
            Term::App(f, a) => go(s, a, false, seen)
                .or_else(|| go(s, f, true, seen))
                .or_else(|| (!in_fn_pos && reducible(s, t)).then_some(t)),
        }
    }
    go(s, t, false, &mut HashSet::new())
}

/// The spine policy. Reduce `App(…App(Abs^m b, a₁)…, a_n)`'s first
/// `k = min(m, n)` arguments only if every one of them:
/// - is a `Var` or `Lit`: always cheap; or
/// - is a closed `Abs`/`Rec`: a static table entry, deduped by hash, so
///   copies cost nothing; or
/// - binds a parameter used at most once in `b`, and not under a lambda
///   left unapplied. Otherwise a capturing closure created once would be
///   created at every use, or on every iteration of a loop inside `b`
///   (GHC's "OnceInLam").
fn reducible(s: &TermStore, spine: Hash) -> bool {
    let (head, args) = unwind(s, spine);
    let k = count_abs(s, head).min(args.len());
    if k == 0 {
        return false;
    }
    let body = peel(s, head, k);
    args[..k].iter().enumerate().all(|(i, &a)| match s.resolve(a) {
        Term::Var(_) | Term::Lit(_) => true,
        Term::Abs(_) | Term::Rec(_) => {
            // a₁ binds the outermost of the k lambdas: Var(k-1) in `b`.
            let param = (k - 1 - i) as u32;
            let (n, under) = occurrences(s, body, param, false, &mut HashMap::new());
            !has_free(s, a, 0, &mut HashMap::new()) || n == 0 || (n == 1 && !under)
        }
        _ => false,
    })
}

fn has_free(s: &TermStore, t: Hash, depth: u32, memo: &mut HashMap<(Hash, u32), bool>) -> bool {
    if let Some(&r) = memo.get(&(t, depth)) {
        return r;
    }
    let r = match *s.resolve(t) {
        Term::Var(i) => i >= depth,
        Term::Lit(_) => false,
        Term::Prim(_, a, b) | Term::App(a, b) => has_free(s, a, depth, memo) || has_free(s, b, depth, memo),
        Term::If(c, x, y) => has_free(s, c, depth, memo) || has_free(s, x, depth, memo) || has_free(s, y, depth, memo),
        Term::Abs(b) | Term::Rec(b) => has_free(s, b, depth + 1, memo),
    };
    memo.insert((t, depth), r);
    r
}

/// Returns `(how many times Var(idx) occurs in t, whether any occurrence is
/// under a lambda or Rec that is not applied right where it stands)`. `under`
/// says whether `t` itself already is.
fn occurrences(s: &TermStore, t: Hash, idx: u32, under: bool, memo: &mut HashMap<(Hash, u32, bool), (usize, bool)>) -> (usize, bool) {
    if let Some(&r) = memo.get(&(t, idx, under)) {
        return r;
    }
    let add = |(a, x): (usize, bool), (b, y): (usize, bool)| (a + b, x || y);
    let r = match *s.resolve(t) {
        Term::Var(i) => if i == idx { (1, under) } else { (0, false) },
        Term::Lit(_) => (0, false),
        Term::Prim(_, a, b) => add(occurrences(s, a, idx, under, memo), occurrences(s, b, idx, under, memo)),
        Term::If(c, x, y) => {
            let cx = add(occurrences(s, c, idx, under, memo), occurrences(s, x, idx, under, memo));
            add(cx, occurrences(s, y, idx, under, memo))
        }
        Term::Abs(b) | Term::Rec(b) => occurrences(s, b, idx + 1, true, memo),
        Term::App(..) => {
            let (head, args) = unwind(s, t);
            let mut acc = (0, false);
            for &a in &args {
                acc = add(acc, occurrences(s, a, idx, under, memo));
            }
            // A literal-lambda head's first min(m, n) lambdas are applied
            // right here, so entering them does not count as going under a
            // lambda.
            let applied = count_abs(s, head).min(args.len());
            let inner = peel(s, head, applied);
            add(acc, occurrences(s, inner, idx + applied as u32, under, memo))
        }
    };
    memo.insert((t, idx, under), r);
    r
}

/// `body[0 := v]` for a `body` under one binder, in a single pass. At depth
/// `d`, `Var(d)` becomes `v` with its free variables raised by `d`, deeper
/// free variables drop by one, and bound ones stay.
fn instantiate(s: &mut TermStore, body: Hash, v: Hash) -> Hash {
    fn go(s: &mut TermStore, t: Hash, d: u32, v: Hash, memo: &mut HashMap<(Hash, u32), Hash>) -> Hash {
        if let Some(&r) = memo.get(&(t, d)) {
            return r;
        }
        let r = match s.resolve(t).clone() {
            Term::Var(i) if i == d => lift(s, v, d, 0, &mut HashMap::new()),
            Term::Var(i) if i > d => s.var(i - 1),
            Term::Var(_) | Term::Lit(_) => t,
            Term::Prim(op, a, b) => {
                let (a, b) = (go(s, a, d, v, memo), go(s, b, d, v, memo));
                s.prim(op, a, b)
            }
            Term::If(c, x, y) => {
                let (c, x, y) = (go(s, c, d, v, memo), go(s, x, d, v, memo), go(s, y, d, v, memo));
                s.if_(c, x, y)
            }
            Term::Abs(b) => {
                let b = go(s, b, d + 1, v, memo);
                s.abs(b)
            }
            Term::App(f, a) => {
                let (f, a) = (go(s, f, d, v, memo), go(s, a, d, v, memo));
                s.app(f, a)
            }
            Term::Rec(b) => {
                let b = go(s, b, d + 1, v, memo);
                s.rec(b)
            }
        };
        memo.insert((t, d), r);
        r
    }
    go(s, body, 0, v, &mut HashMap::new())
}

/// `t` with every variable free at `depth` (index `>= depth`) raised by `by`.
fn lift(s: &mut TermStore, t: Hash, by: u32, depth: u32, memo: &mut HashMap<(Hash, u32), Hash>) -> Hash {
    if by == 0 {
        return t;
    }
    if let Some(&r) = memo.get(&(t, depth)) {
        return r;
    }
    let r = match s.resolve(t).clone() {
        Term::Var(i) if i >= depth => s.var(i + by),
        Term::Var(_) | Term::Lit(_) => t,
        Term::Prim(op, a, b) => {
            let (a, b) = (lift(s, a, by, depth, memo), lift(s, b, by, depth, memo));
            s.prim(op, a, b)
        }
        Term::If(c, x, y) => {
            let (c, x, y) = (lift(s, c, by, depth, memo), lift(s, x, by, depth, memo), lift(s, y, by, depth, memo));
            s.if_(c, x, y)
        }
        Term::Abs(b) => {
            let b = lift(s, b, by, depth + 1, memo);
            s.abs(b)
        }
        Term::App(f, a) => {
            let (f, a) = (lift(s, f, by, depth, memo), lift(s, a, by, depth, memo));
            s.app(f, a)
        }
        Term::Rec(b) => {
            let b = lift(s, b, by, depth + 1, memo);
            s.rec(b)
        }
    };
    memo.insert((t, depth), r);
    r
}

/// `t` with every occurrence of `target` replaced by `with`, in one pass.
fn replace(s: &mut TermStore, t: Hash, target: Hash, with: Hash, memo: &mut HashMap<Hash, Hash>) -> Hash {
    if t == target {
        return with;
    }
    if let Some(&r) = memo.get(&t) {
        return r;
    }
    let r = match s.resolve(t).clone() {
        Term::Var(_) | Term::Lit(_) => t,
        Term::Prim(op, a, b) => {
            let (a, b) = (replace(s, a, target, with, memo), replace(s, b, target, with, memo));
            s.prim(op, a, b)
        }
        Term::If(c, x, y) => {
            let (c, x, y) = (replace(s, c, target, with, memo), replace(s, x, target, with, memo), replace(s, y, target, with, memo));
            s.if_(c, x, y)
        }
        Term::Abs(b) => {
            let b = replace(s, b, target, with, memo);
            s.abs(b)
        }
        Term::App(f, a) => {
            let (f, a) = (replace(s, f, target, with, memo), replace(s, a, target, with, memo));
            s.app(f, a)
        }
        Term::Rec(b) => {
            let b = replace(s, b, target, with, memo);
            s.rec(b)
        }
    };
    memo.insert(t, r);
    r
}

fn size(s: &TermStore, t: Hash) -> usize {
    let mut seen = HashSet::new();
    let mut stack = vec![t];
    while let Some(u) = stack.pop() {
        if !seen.insert(u) || seen.len() > MAX_NODES {
            continue;
        }
        match *s.resolve(u) {
            Term::Var(_) | Term::Lit(_) => {}
            Term::Prim(_, a, b) | Term::App(a, b) => stack.extend([a, b]),
            Term::If(c, x, y) => stack.extend([c, x, y]),
            Term::Abs(b) | Term::Rec(b) => stack.push(b),
        }
    }
    seen.len()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec_check::check;
    use crate::term::PrimOp;
}
```

  Run `cargo build` [0 errors]. If a borrow error comes from
  `match s.resolve(t).clone() { .. s.var(..) .. }`, bind the clone first
  (`let term = s.resolve(t).clone(); match term { .. }`).

- [ ] **Step 3: Write the specialiser's tests.**

```rust
    fn corpus(name: &str) -> (TermStore, Hash) {
        let (_, s, h) = crate::test_corpus::terms().into_iter().find(|(n, ..)| *n == name).unwrap();
        (s, h)
    }

    /// Specialises `h` and requires the checker to accept the result.
    fn specialise_checked(s: &TermStore, h: Hash) -> Specialised {
        let sp = specialise(s, h);
        assert_eq!(check(s, h, &sp.trace, sp.term), Ok(()), "the checker rejected the specialiser's own trace");
        sp
    }

    #[test]
    fn a_known_partial_application_becomes_plain_arithmetic() {
        // caller (add acc) n  ->  acc + n, in four steps: add acc, then
        // the two-argument caller spine, then (\y. acc + y) n.
        let (s, h) = corpus("partial_application_loop");
        let sp = specialise_checked(&s, h);
        assert_eq!(sp.trace.len(), 4, "{:?}", sp.trace);
        // rec f n acc = if n <= 0 then acc else f (n-1) (acc+n):
        // acc = Var(0), n = Var(1), f = Var(2).
        let mut w = TermStore::new();
        let (acc, n, f, zero, one) = (w.var(0), w.var(1), w.var(2), w.lit(0), w.lit(1));
        let cond = w.prim(PrimOp::Le, n, zero);
        let nm1 = w.prim(PrimOp::Sub, n, one);
        let sum = w.prim(PrimOp::Add, acc, n);
        let call = w.app2(f, nm1, sum);
        let body = w.if_(cond, acc, call);
        let inner = w.abs(body);
        let outer = w.abs(inner);
        assert_eq!(sp.term, w.rec(outer));
    }

    #[test]
    fn a_closure_created_and_called_at_once_is_reduced() {
        let (s, h) = corpus("capturing_closure_loop");
        let sp = specialise_checked(&s, h);
        assert_eq!(sp.trace.len(), 1, "{:?}", sp.trace);
        for args in [[0, 0], [1, 0], [5, 3], [100, -7]] {
            assert_eq!(crate::eval::apply_term(&sp.store, sp.term, &args), crate::eval::apply_term(&s, h, &args), "args={args:?}");
        }
    }

    #[test]
    fn a_rec_in_head_position_is_left_alone() {
        let (s, h) = corpus("closure_typed_loop_carried_parameter_loop");
        let sp = specialise_checked(&s, h);
        assert!(sp.trace.is_empty(), "{:?}", sp.trace);
        assert_eq!(sp.term, h);
    }

    /// `\x. (\g. rec f n. if n <= 0 then 0 else g n + f (n-1)) G`, where
    /// `G` is `\y. y + x` (capturing) or `\y. y + 1` (closed). Under the
    /// Rec's lambda: n = Var(0), f = Var(1), g = Var(2), x = Var(3).
    fn loop_using(s: &mut TermStore, capturing: bool) -> Hash {
        let (v0, v1, v2, zero, one) = (s.var(0), s.var(1), s.var(2), s.lit(0), s.lit(1));
        let cond = s.prim(PrimOp::Le, v0, zero);
        let gn = s.app(v2, v0);
        let nm1 = s.prim(PrimOp::Sub, v0, one);
        let fn1 = s.app(v1, nm1);
        let sum = s.prim(PrimOp::Add, gn, fn1);
        let body = s.if_(cond, zero, sum);
        let abs = s.abs(body);
        let rec = s.rec(abs);
        let lam = s.abs(rec);
        let g_body = if capturing { s.prim(PrimOp::Add, v0, v1) } else { s.prim(PrimOp::Add, v0, one) };
        let g = s.abs(g_body);
        let redex = s.app(lam, g);
        s.abs(redex)
    }

    #[test]
    fn a_capturing_closure_is_not_moved_into_a_loop_body() {
        let mut s = TermStore::new();
        let h = loop_using(&mut s, true);
        let sp = specialise_checked(&s, h);
        assert!(sp.trace.is_empty(), "{:?}", sp.trace);
        assert_eq!(sp.term, h);
    }

    #[test]
    fn a_closed_closure_is_moved_into_a_loop_body() {
        let mut s = TermStore::new();
        let h = loop_using(&mut s, false);
        let sp = specialise_checked(&s, h);
        assert_eq!(sp.trace.len(), 1, "{:?}", sp.trace);
    }

    #[test]
    fn a_non_value_argument_is_not_substituted() {
        // (\x. x + x) (1 / 0): substituting would evaluate the error twice
        // (harmless) but also, in general, change evaluation order. βv
        // never reduces it.
        let mut s = TermStore::new();
        let (v0, zero, one) = (s.var(0), s.lit(0), s.lit(1));
        let body = s.prim(PrimOp::Add, v0, v0);
        let lam = s.abs(body);
        let div = s.prim(PrimOp::Div, one, zero);
        let h = s.app(lam, div);
        let sp = specialise_checked(&s, h);
        assert!(sp.trace.is_empty());
    }

    #[test]
    fn a_divergent_term_stops_at_the_step_limit() {
        // (\x. x x) (\x. x x) reduces to itself, forever.
        let mut s = TermStore::new();
        let v0 = s.var(0);
        let xx = s.app(v0, v0);
        let w = s.abs(xx);
        let omega = s.app(w, w);
        let sp = specialise_checked(&s, omega);
        assert_eq!(sp.trace.len(), MAX_STEPS);
        assert_eq!(sp.term, omega);
    }

    #[test]
    fn every_corpus_term_specialises_to_something_the_checker_accepts_and_that_evaluates_the_same() {
        for (name, s, h) in crate::test_corpus::terms() {
            let sp = specialise_checked(&s, h);
            let arity = crate::compile::peel(&s, h).map_or(0, |(k, ..)| k);
            for x in [0i64, 1, 2, 5, -3] {
                let args = vec![x; arity];
                assert_eq!(crate::eval::apply_term(&sp.store, sp.term, &args), crate::eval::apply_term(&s, h, &args), "{name} args={args:?}");
            }
        }
    }
```

  Note on the last test: `compile::peel` is `pub(crate)`, which is allowed
  in the specialiser's tests; only the code above the tests must stay
  independent. If a corpus term's arity from `peel` doesn't match how
  `eval::apply_term` must be called for it, skip that term and name it in
  a comment. Don't weaken the comparison.

  Run `cargo test --lib specialise` [9 pass].

- [ ] **Step 4: Teeth.**
  - In `lift`, change `s.var(i + by)` to `s.var(i + by + 1)`:
    `a_known_partial_application_becomes_plain_arithmetic` must fail
    inside `specialise_checked` with "the checker rejected the
    specialiser's own trace". This is the planted specialiser bug the
    checker catches. Revert.
  - In `reducible`, change `(n == 1 && !under)` to `n <= 1`:
    `a_capturing_closure_is_not_moved_into_a_loop_body` fails. Revert.
  - In `find_spine`, drop the `!in_fn_pos &&` guard. Run the tests and
    record what happens: some trace length changes, or nothing does. If
    nothing fails, say so in the report and explain why; don't invent a
    failing test. Revert.

- [ ] **Step 5: Full validation** (checks 1-9). Lib+bins goes up by 9.
- [ ] **Step 6: Commit and push.** Message: "Add the untrusted βv
  specialiser with the spine policy".

---

### Task 3: The pipeline driver, JIT integration and specialised goldens

**Files:**
- Modify: `src/compile.rs`, `src/jit.rs`, `tests/golden_wat.rs`
- Create: `tests/golden/partial_application_loop_specialised.wat`,
  `tests/golden/capturing_closure_loop_specialised.wat` (by `UPDATE_GOLDEN`)

**Interfaces:**
- Consumes: `specialise::{specialise, Specialised}`, `spec_check::check`,
  `try_compile`.
- Produces:
  ```rust
  pub struct Compiled { pub frag: CompiledFragment, pub specialised: Option<(TermStore, Hash)> }
  pub fn compile_specialised(store: &TermStore, h: Hash) -> Option<Compiled>
  pub fn spec_check_failures() -> usize
  ```
  Also `jit::Stats::specialised: u64`.

- [ ] **Step 1: Add the driver to `src/compile.rs`,** after
  `try_compile`.

```rust
static SPEC_CHECK_FAILURES: AtomicUsize = AtomicUsize::new(0);

/// How many times, process-wide, `compile_specialised` discarded a
/// specialisation because `spec_check::check` rejected its trace. Every
/// such case is a specialiser bug. The release-mode compile fuzzer asserts
/// it is 0, as with `ir_validation_failures`.
pub fn spec_check_failures() -> usize {
    SPEC_CHECK_FAILURES.load(Ordering::Relaxed)
}

/// What `compile_specialised` compiled.
pub struct Compiled {
    pub frag: CompiledFragment,
    /// `Some((store, h'))` when the fragment was compiled from `h'`, a
    /// specialisation of `h` that `spec_check::check` accepted. `None` when
    /// it was compiled from `h` itself.
    pub specialised: Option<(TermStore, Hash)>,
}

/// The one pipeline driver: specialise `h` (`specialise.rs`, untrusted),
/// check the certificate (`spec_check.rs`, trusted and independent), and
/// compile the result with `try_compile`. The passes stay separate:
/// `try_compile` is a pure translation whose module decompiles to exactly
/// the term it was given. This function adds only the certificate-checked
/// step from `h` to that term. If the specialised term does not compile,
/// `h` is tried instead.
///
/// The claim for a specialised result: its module decompiles to `h'`, and
/// `h' ≡ h` by a checked βv trace. That equivalence is not kernel-checked
/// (RELATED_WORK.md §37).
pub fn compile_specialised(store: &TermStore, h: Hash) -> Option<Compiled> {
    compile_candidate(store, h, crate::specialise::specialise(store, h))
}

fn compile_candidate(store: &TermStore, h: Hash, sp: crate::specialise::Specialised) -> Option<Compiled> {
    if !sp.trace.is_empty() {
        match crate::spec_check::check(store, h, &sp.trace, sp.term) {
            // `sp.store` is the specialiser's, but it can't lie about
            // `sp.term`: a store's hashes are the content hashes of what it
            // holds, and the checker accepted that hash.
            Ok(()) => {
                if let Some(frag) = try_compile(&sp.store, sp.term) {
                    return Some(Compiled { frag, specialised: Some((sp.store, sp.term)) });
                }
            }
            Err(e) => {
                SPEC_CHECK_FAILURES.fetch_add(1, Ordering::Relaxed);
                if cfg!(debug_assertions) {
                    panic!("the specialiser produced a trace the checker rejects for {h:?}: step {}: {}", e.step, e.reason);
                }
            }
        }
    }
    try_compile(store, h).map(|frag| Compiled { frag, specialised: None })
}
```

  Add tests to `compile.rs`'s test module. It already has
  `fn instantiate(wat: &str) -> (wasmtime::Store<()>, wasmtime::Instance)`.

```rust
    fn corpus(name: &str) -> (TermStore, Hash) {
        let (_, s, h) = crate::test_corpus::terms().into_iter().find(|(n, ..)| *n == name).unwrap();
        (s, h)
    }

    #[test]
    fn compile_specialised_compiles_the_checked_specialisation() {
        let (s, h) = corpus("partial_application_loop");
        let c = compile_specialised(&s, h).unwrap();
        assert!(c.specialised.is_some());
        // No closure is left: no table dispatch and no allocator.
        assert!(!c.frag.wat.contains("call_indirect"), "{}", c.frag.wat);
        assert!(!c.frag.wat.contains("$alloc"), "{}", c.frag.wat);
        let (mut store, instance) = instantiate(&c.frag.wat);
        let f = instance.get_typed_func::<(i64, i64), i64>(&mut store, "f").unwrap();
        for (n, acc) in [(0, 0), (1, 0), (5, 3), (100, -7)] {
            assert_eq!(f.call(&mut store, (n, acc)).unwrap(), crate::eval::apply_term(&s, h, &[n, acc]).unwrap(), "n={n} acc={acc}");
        }
    }

    #[test]
    fn a_term_with_nothing_to_specialise_compiles_exactly_as_try_compile_does() {
        let (s, h) = corpus("factorial");
        let c = compile_specialised(&s, h).unwrap();
        assert!(c.specialised.is_none());
        assert_eq!(c.frag.wat, try_compile(&s, h).unwrap().wat);
    }

    #[test]
    #[should_panic(expected = "the specialiser produced a trace the checker rejects")]
    fn a_trace_the_checker_rejects_panics_in_debug() {
        let (s, h) = corpus("partial_application_loop");
        let mut sp = crate::specialise::specialise(&s, h);
        sp.term = sp.store.lit(0); // a real term in the store, but not what the trace reaches
        compile_candidate(&s, h, sp);
    }
```

  Run `cargo test --lib compile_specialised a_term_with_nothing a_trace_the_checker` [3 pass].

- [ ] **Step 2: Use the driver in `src/jit.rs`.**
  - In `compile_verify_and_apply`, replace
    `let Some(frag) = try_compile(terms, h) else {` with
    `let Some(crate::compile::Compiled { frag, specialised }) = crate::compile::compile_specialised(terms, h) else {`.
  - Keep `verify(terms, h, ..)` exactly as it is: it compares against the
    original `h`, which is the dynamic check independent of the rewrite.
  - Replace `let proof = self.kernel_verify(terms, h, frag.arity);` with:

```rust
            // The kernel theorems model the structure of the term that was
            // compiled, so for a specialised fragment they are proved about
            // `h'`. `h' ≡ h` itself is certificate-checked, not
            // kernel-checked (RELATED_WORK.md §37).
            let (proof_store, proof_term) = specialised.as_ref().map_or((terms, h), |(s, t)| (s, *t));
            let proof = self.kernel_verify(proof_store, proof_term, frag.arity);
```

  - Add to `Stats`:

```rust
    /// Of `compiled`, how many were compiled from a certificate-checked
    /// specialisation (`compile::compile_specialised`) rather than from the
    /// term itself.
    pub specialised: u64,
```

    Increment it next to `self.stats.compiled += 1;` when
    `specialised.is_some()`.
  - Remove the now-unused `use crate::compile::try_compile;` if nothing
    else uses it, and update the module docs line that names
    `compile::try_compile` as the compile step so it names
    `compile::compile_specialised`. Add one sentence with the trust claim
    from the driver's docs.
  - Add a test to `jit.rs`'s test module:

```rust
    #[test]
    fn a_known_partial_application_is_installed_specialised_with_a_universal_proof() {
        let (_, s, h) = crate::test_corpus::terms().into_iter().find(|(n, ..)| *n == "partial_application_loop").unwrap();
        let mut jit = JitEngine::new();
        for args in [[0, 0], [1, 0], [5, 3], [100, -7]] {
            assert_eq!(jit.apply(&s, h, &args), eval::apply_term(&s, h, &args), "args={args:?}");
        }
        assert_eq!((jit.stats.compiled, jit.stats.specialised), (1, 1));
        assert_eq!(jit.proof_strength(h), ProofStrength::Universal);
    }
```

  (Use whatever `eval` import the test module already has.) Run
  `cargo test --lib a_known_partial_application_is_installed` [pass].

- [ ] **Step 3: Specialised goldens.** In `tests/golden_wat.rs`, factor
  the compare-or-write loop body into
  `fn check_golden(dir: &Path, name: &str, got: &str, update: bool, changed: &mut Vec<String>)`.
  It writes when `update`, and otherwise pushes `name` onto `changed` if the
  file differs (CRLF-normalised). Then add:

```rust
#[test]
fn specialised_benchmark_terms_lower_to_their_golden_wat() {
    let update = std::env::var_os("UPDATE_GOLDEN").is_some();
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("golden");
    let mut changed = Vec::new();
    let terms: [(&str, fn(&mut TermStore) -> Hash); 2] =
        [("partial_application_loop", common::partial_application_loop), ("capturing_closure_loop", common::capturing_closure_loop)];
    for (name, build) in terms {
        let mut s = TermStore::new();
        let h = build(&mut s);
        let c = tatic::compile::compile_specialised(&s, h).unwrap_or_else(|| panic!("{name} should compile"));
        assert!(c.specialised.is_some(), "{name} should be specialised");
        check_golden(&dir, &format!("{name}_specialised"), &c.frag.wat, update, &mut changed);
    }
    assert!(changed.is_empty(), "emitted WAT changed for {changed:?}; if intended, rerun with UPDATE_GOLDEN=1 and review the diff");
}
```

  Run `UPDATE_GOLDEN=1 cargo test --test golden_wat`, then
  `cargo test --test golden_wat` [2 pass]. `git status -- tests/golden`
  must show exactly two new untracked files and no modified ones. Read
  both new files. `partial_application_loop_specialised.wat` should have
  one `$f` loop, no table and no `$alloc`. Paste its `$f` body into the
  report.

- [ ] **Step 4: Teeth.**
  - In `compile_candidate`, change `Ok(()) =>` to `_ =>` and delete the
    `Err` arm. `a_trace_the_checker_rejects_panics_in_debug` must fail.
    Revert.
  - In `jit.rs`, pass `(terms, h)` to `kernel_verify` unconditionally. Run
    the new JIT test and record the result. If it still passes (because
    `h` also has a universal proof, as the probe found), say so, and keep
    the change reverted. The check is there for honesty, not for a
    failing test.

- [ ] **Step 5: Full validation** (checks 1-9). Lib+bins goes up by 4 and
  golden goes to 2. For check 6, record the new `JIT stats` line. If
  `compiled` or `declined_no_universal_proof` changed, find which demo
  term changed and explain it in the report.
- [ ] **Step 6: Commit and push.** Message: "Compile through a
  specialise-then-check driver; the JIT installs checked
  specialisations".

---

### Task 4: Mutation test and differential fuzz

**Files:**
- Modify: `src/spec_check.rs` (tests), `tests/compile_fuzz.rs`

**Interfaces:**
- Consumes: `specialise::specialise` (in tests), `spec_check::check`,
  `compile::spec_check_failures`, `eval::apply_term`.

- [ ] **Step 1: The checker mutation test,** in `spec_check.rs`'s test
  module. Tests may use the specialiser.

```rust
    /// Every distinct subterm of `t`.
    fn subterms(s: &TermStore, t: Hash) -> Vec<Hash> {
        let mut seen = HashSet::new();
        let mut stack = vec![t];
        let mut out = Vec::new();
        while let Some(u) = stack.pop() {
            if seen.insert(u) {
                out.push(u);
                stack.extend(children(s.resolve(u)));
            }
        }
        out
    }

    /// `t` with its first `Var` or `Lit` leaf (in `subterms` order) bumped
    /// by one, built in `s`. `None` if `t` has neither.
    fn bump_one_leaf(s: &mut TermStore, t: Hash) -> Option<Hash> {
        let leaf = subterms(s, t).into_iter().find(|&u| matches!(s.resolve(u), Term::Var(_) | Term::Lit(_)))?;
        let bumped = match *s.resolve(leaf) {
            Term::Var(i) => s.var(i + 1),
            Term::Lit(n) => s.lit(n.wrapping_add(1)),
            _ => unreachable!(),
        };
        Some(replace_all(s, t, leaf, bumped, &mut HashMap::new()))
    }

    #[test]
    fn every_mutated_certificate_is_rejected_unless_it_really_replays_to_its_claim() {
        let mut counts = [0usize; 5];
        for (name, s, h) in crate::test_corpus::terms() {
            let sp = crate::specialise::specialise(&s, h);
            if sp.trace.is_empty() {
                continue;
            }
            let t = &sp.trace;
            // 1. Drop a step.
            for i in 0..t.len() {
                let mut m = t.clone();
                m.remove(i);
                assert!(check(&s, h, &m, sp.term).is_err(), "{name}: dropping step {i} was accepted");
                counts[0] += 1;
            }
            // 2. Swap adjacent steps. Two steps on disjoint redexes commute,
            // so acceptance is allowed, but only if the claim is also
            // reached by an honest replay, which the unmutated order is.
            for i in 0..t.len().saturating_sub(1) {
                let mut m = t.clone();
                m.swap(i, i + 1);
                if m != *t && check(&s, h, &m, sp.term).is_ok() {
                    assert_eq!(check(&s, h, t, sp.term), Ok(()), "{name}: swap {i} accepted, but the original trace is not");
                }
                counts[1] += 1;
            }
            // 3. Retarget a step to another subterm of the source.
            let subs = subterms(&s, h);
            for i in 0..t.len() {
                let Step::BetaV { redex } = t[i];
                for &other in subs.iter().filter(|&&u| u != redex).take(8) {
                    let mut m = t.clone();
                    m[i] = Step::BetaV { redex: other };
                    assert!(check(&s, h, &m, sp.term).is_err(), "{name}: retargeting step {i} was accepted");
                    counts[2] += 1;
                }
            }
            // 4. Change one leaf of the claim.
            let mut scratch = TermStore::new();
            let claim = copy(&sp.store, &mut scratch, sp.term, &mut HashMap::new());
            if let Some(bad) = bump_one_leaf(&mut scratch, claim) {
                assert!(check(&s, h, t, bad).is_err(), "{name}: a changed claim was accepted");
                counts[3] += 1;
            }
            // 5. Truncate the trace.
            for len in 0..t.len() {
                assert!(check(&s, h, &t[..len], sp.term).is_err(), "{name}: truncation to {len} was accepted");
                counts[4] += 1;
            }
        }
        assert!(counts.iter().all(|&c| c > 0), "every mutation kind must run at least once: {counts:?}");
    }
```

  Kind 3 asserts rejection outright. A retargeted step could in principle
  hit a different valid redex and still reach the same claim. If that
  happens on the corpus, change that assertion to the same "only if an
  honest replay exists" form as kind 2, and explain it in the report. Don't
  delete the kind.

  Kinds 1 and 5 assume no step is an identity. `a_divergent_term...` is not
  in the corpus, so that holds. Add
  `assert!(t.iter().all(|&Step::BetaV { redex }| { let c = ...; }))` only
  if a failure shows it's needed.

  Run `cargo test --lib every_mutated_certificate` [pass]. Report `counts`
  (print them with `eprintln!`).

- [ ] **Step 2: The differential fuzz,** in `tests/compile_fuzz.rs`.
  Add `use tatic::{spec_check, specialise};`. Add a generator of
  redex-rich terms that, unlike `random_arith_op`, includes `Div`/`Mod`.

```rust
/// An Int-valued expression over `scope` variables that is full of βv
/// redexes: literal lambdas applied to values (literals, variables,
/// closed or capturing lambdas), two-argument spines, and redexes whose
/// argument is not a value (which must stay put). `Div`/`Mod` are
/// included so errors are exercised. There's no `Rec` and every applied
/// lambda is fresh, so every term terminates.
fn gen_redex_rich(rng: &mut Rng, s: &mut TermStore, scope: u32, fuel: u32) -> Hash {
    let leaf = |rng: &mut Rng, s: &mut TermStore| {
        if scope > 0 && rng.below(2) == 0 { s.var(rng.below(scope)) } else { s.lit(rng.i64_range(-3, MAX_LIT)) }
    };
    if fuel == 0 {
        return leaf(rng, s);
    }
    match rng.below(8) {
        0 => leaf(rng, s),
        1 => {
            let op = [PrimOp::Add, PrimOp::Sub, PrimOp::Mul, PrimOp::Div, PrimOp::Mod, PrimOp::Lt][rng.below(6) as usize];
            let a = gen_redex_rich(rng, s, scope, fuel - 1);
            let b = gen_redex_rich(rng, s, scope, fuel - 1);
            s.prim(op, a, b)
        }
        2 => {
            let c = gen_redex_rich(rng, s, scope, fuel - 1);
            let t = gen_redex_rich(rng, s, scope, fuel - 1);
            let e = gen_redex_rich(rng, s, scope, fuel - 1);
            s.if_(c, t, e)
        }
        3 => {
            // (\x. e) v, with v a leaf.
            let body = gen_redex_rich(rng, s, scope + 1, fuel - 1);
            let lam = s.abs(body);
            let v = leaf(rng, s);
            s.app(lam, v)
        }
        4 => {
            // (\x. e) a, with a not necessarily a value.
            let body = gen_redex_rich(rng, s, scope + 1, fuel - 1);
            let lam = s.abs(body);
            let a = gen_redex_rich(rng, s, scope, fuel - 1);
            s.app(lam, a)
        }
        5 => {
            // (\g. g e1 + e2) (\y. e3): a closure argument, called once,
            // possibly capturing. Inside \g, Var(0) is g.
            let g = s.var(0);
            let e1 = gen_redex_rich(rng, s, scope + 1, fuel - 1);
            let call = s.app(g, e1);
            let e2 = gen_redex_rich(rng, s, scope + 1, fuel - 1);
            let body = s.prim(PrimOp::Add, call, e2);
            let lam = s.abs(body);
            let fbody = gen_redex_rich(rng, s, scope + 1, fuel - 1);
            let f = s.abs(fbody);
            s.app(lam, f)
        }
        6 => {
            // (\a b. e) v1 v2
            let body = gen_redex_rich(rng, s, scope + 2, fuel - 1);
            let inner = s.abs(body);
            let lam = s.abs(inner);
            let (v1, v2) = (leaf(rng, s), leaf(rng, s));
            s.app2(lam, v1, v2)
        }
        _ => {
            // (\a b. e) v1: a partial application, then applied to v2 via a caller.
            let body = gen_redex_rich(rng, s, scope + 2, fuel - 1);
            let inner = s.abs(body);
            let add_like = s.abs(inner);
            let v1 = leaf(rng, s);
            let partial = s.app(add_like, v1);
            let (g, z) = (s.var(1), s.var(0));
            let gz = s.app(g, z);
            let c_inner = s.abs(gz);
            let caller = s.abs(c_inner);
            let v2 = leaf(rng, s);
            s.app2(caller, partial, v2)
        }
    }
}

#[test]
fn specialisation_is_checked_and_preserves_meaning_on_random_terms() {
    const SEEDS: u64 = 1000;
    const SAMPLE_VALUES: [i64; 7] = [0, 1, -1, 2, -3, 10, -20];
    let mut specialised = 0u32;
    for seed in 0..SEEDS {
        let mut rng = Rng::new(0x5BEC_1A11_u64 ^ seed);
        let mut s = TermStore::new();
        // Half redex-rich terms, half the existing programs (recursion, closures).
        let (h, arity) = if seed % 2 == 0 {
            let e = gen_redex_rich(&mut rng, &mut s, 2, 4);
            let inner = s.abs(e);
            (s.abs(inner), 2)
        } else {
            let (h, arity, _) = gen_program(&mut rng, &mut s);
            (h, arity)
        };
        let sp = specialise::specialise(&s, h);
        assert_eq!(spec_check::check(&s, h, &sp.trace, sp.term), Ok(()), "seed={seed}: the checker rejected the specialiser's trace");
        if !sp.trace.is_empty() {
            specialised += 1;
        }
        let mut args = vec![0i64; arity];
        for trial in 0..8 {
            for a in args.iter_mut() {
                *a = SAMPLE_VALUES[rng.below(SAMPLE_VALUES.len() as u32) as usize];
            }
            // Exact equality, including which error: βv moves only values,
            // which have no effects, so it can't reorder or remove an error.
            assert_eq!(
                eval::apply_term(&sp.store, sp.term, &args),
                eval::apply_term(&s, h, &args),
                "seed={seed} trial={trial} args={args:?}"
            );
        }
    }
    eprintln!("specialisation fuzz: {specialised}/{SEEDS} terms specialised");
    assert!(specialised > SEEDS as u32 / 4, "too few terms specialised ({specialised}/{SEEDS}); check gen_redex_rich");
    assert_eq!(compile::spec_check_failures(), 0);
    assert_no_ir_failures();
}
```

  Also add `assert_eq!(compile::spec_check_failures(), 0, "...")` inside
  `assert_no_ir_failures`, since the existing JIT-driven fuzz now goes
  through the driver.

  Run `cargo test --release --test compile_fuzz` [6 pass]. Report the
  printed `specialised` count.

  If `eval::apply_term` can recurse deeply enough on these terms to
  overflow the stack, lower the generator's fuel from 4 to 3 and say so.

- [ ] **Step 3: Teeth.**
  - Planted specialiser bug: in `specialise.rs`'s `instantiate`, change
    `Term::Var(i) if i > d => s.var(i - 1)` to `s.var(i)`. The fuzz must
    fail with "the checker rejected the specialiser's trace". Revert.
  - Planted checker bug: in `spec_check.rs`'s `check`, delete the value
    `matches!` guard. The mutation test or a unit test must fail. Name
    which one. Revert.
  - Semantic teeth: a βv-violating rewrite has to be rejected by the
    checker, not merely "noticed" by `eval`. Show this by temporarily
    allowing `Term::Prim(..)` arguments in *both* the checker's value guard
    and the specialiser's `reducible`, so the pair agrees on an unsound
    step. The fuzz's `eval` equality must then fail on some seed with
    `Div` (an error moved or dropped). This proves the differential
    comparison has teeth of its own. Revert both.

- [ ] **Step 4: Full validation** (checks 1-9). Lib+bins goes up by 1 and
  compile_fuzz goes to 6.
- [ ] **Step 5: Commit and push.** Message: "Mutation-test the
  certificate checker and fuzz specialisation against the interpreter".

---

### Task 5: Benches and docs

**Files:**
- Modify: `RELATED_WORK.md` (new §37; §36 note), `README.md`,
  `docs/superpowers/specs/2026-09-24-closure-specialisation-design.md`
  (status), `docs/superpowers/specs/2026-09-23-jit-ir-design.md` (future
  work), `benches/common.rs` (fixture docs)

- [ ] **Step 1: Measure.** Check for other heavy processes first
  (`tasklist | grep -iE "cargo|rustc|training|selfplay"`). Build the bench
  binary on this branch and on `main` (use a worktree at
  `target/base-build` or `git stash`, whichever you prefer; delete
  `target/base-build` afterwards). Run each three times, interleaved, at
  BelowNormal priority:
  `cargo bench --bench execution -- 'partial_application_loop|capturing_closure_loop|closure_typed' --warm-up-time 1 --measurement-time 3`.
  Record the best-of-three medians for each bar, and whether the machine
  was shared.

- [ ] **Step 2: RELATED_WORK.md §37,** "Closure specialisation by
  certificate-checked βv", placed before `## Sources`. Follow §36's
  structure: what was slow, the options, what changed, how it was checked,
  the cost. It must include:
  - The trust-model survey and verdict. The options were A (a trusted
    normaliser), B (an NbE checker), C (a kernel proof) and D (certificate
    replay). The systems compared: CompCert and CakeML (proven inliners),
    CertiCoq ("Shrink fast correctly!"), Œuf (denote and `reflexivity`),
    Tristan–Govereau–Morrisett PLDI'11 (normalising validation), Crellvm
    PLDI'18 (credible compilation: the pass emits hints, a checker checks
    them), Alive2 (intraprocedural, so not a fit), and GHC (a trusted
    simplifier plus Core Lint).
  - The probe finding: `denote` covers `h` and `h'`, but each theorem is
    per term (`Ev_h`), so C needs a new `Ev_h → Ev_h'` builder. Hence D now
    and C later, with the trace as C's proof outline.
  - Plotkin 1975, βv soundness in call-by-value, and why full β is unsound
    here (`(\x. 0)(1/0)`).
  - Hash-addressed, all-occurrences steps as a weak form of Lévy's family
    reduction (same syntax, not same origin). The optimal-reduction
    verdict: not applicable (full β; it minimises normalisation steps, not
    residual run-time cost; Asperti–Mairson's non-elementary bookkeeping).
    Cite Lévy 1978, Lamping 1990, Asperti–Mairson 1998, Balabonski
    ICFP'13/POPL'12, Barenbaum–Bonelli FSCD'17, and Peyton Jones & Marlow
    2002 for "OnceInLam".
  - The placement decision: a separate driver, because `try_compile` tests
    rely on literal-lambda redexes.
  - How it was checked: the unit tests, the mutation counts, the fuzz
    count and the teeth from Tasks 1-4.
  - The cost: Step 1's numbers, plus the controls.
  - The allocator probe's result (spec future work), as one line pointing
    to the IR spec.

  Add the new URLs to `## Sources`:
  - https://en.wikipedia.org/wiki/Reduction_strategy
  - https://arxiv.org/pdf/1701.04240
  - https://usr.lmf.cnrs.fr/~blsk/Publications/Balabonski-WeakOptimality-ICFP13.pdf
  - https://public.lmf.cnrs.fr/~blsk/Publications/Balabonski-FullLaziness-POPL12.pdf
  - https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.9
  - https://www.researchgate.net/publication/222245890_Parallel_Beta_Reduction_Is_Not_Elementary_Recursive

- [ ] **Step 3: Other docs.**
  - §36: one sentence saying the `capturing_closure_loop` bench goes
    through the JIT and now measures specialisation, while lambda lifting
    stays covered by its `try_compile`-level test.
  - `benches/common.rs`: the docs of `capturing_closure_loop` and
    `partial_application_loop` now say what the JIT does to each (see
    §37).
  - The IR spec's "Future work" closure-specialisation bullet points to
    the new spec and says V3 is done.
  - The new spec's status becomes "V3 implemented (RELATED_WORK.md §37);
    V1 and C open".
  - README: find where the pipeline and trust are described (`grep -n
    "try_compile\|decompile" README.md`). Add the driver and its trust
    claim in the same style, and list the new fuzz test in the Fuzzing
    section.

- [ ] **Step 4: Full validation** (checks 1-9).
- [ ] **Step 5: Commit and push.** Message: "Document closure
  specialisation (§37) and its measured cost".
