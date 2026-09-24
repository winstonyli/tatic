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
}
