//! The trusted half of closure specialisation. It replays a certificate (a
//! trace of βv steps) from the source term, and accepts only if every step
//! is a real βv contraction and the replay ends at exactly the claimed
//! term. See `docs/superpowers/specs/2026-09-24-closure-specialisation-design.md`.
//!
//! Why βv and nothing more: `eval` is call-by-value, with errors
//! (`DivByZero`, `TypeError`, ...) and unbounded `Rec`, so full β is
//! unsound (`(\x. 0) (1/0)` fails; `0` doesn't). For a value `V` (a bound
//! `Var`, `Lit`, `Abs`, `Rec`), `(\. M) V = M[0 := V]` is an observational
//! equivalence closed under every context (Plotkin 1975). So a step may
//! rewrite anywhere, including under binders. Because an equal subterm
//! may be replaced in any context, a step also rewrites every occurrence
//! at once. `App(Rec, V)` is never a redex: `Rec` is never unfolded.
//! The source must be closed, so that every `Var` is bound and so a value
//! (see `check`).
//!
//! This file is independent of the specialiser by construction. It uses
//! only `crate::lang::term` and `std` (a test enforces this) and has its own
//! substitution, so a bug in `specialise.rs`'s substitution cannot be
//! mirrored here.

use crate::lang::term::{Hash, Term, TermStore};
use hashbrown::{HashMap, HashSet};

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
    // A `Var` is a value only when it is bound: `eval` starts from an empty
    // environment, so an unbound one is `Err(UnboundVariable)`, and
    // `(\x. 0) v5` would contract an error away. In a closed source every
    // `Var` in every occurrence is bound by an enclosing binder, and βv
    // keeps a term closed, so requiring it here makes every `Var` a value.
    if has_free_var(store, h, 0, &mut HashMap::new()) {
        return fail(0, "source term has free variables");
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
        // A `Var` here is bound, since the source is closed.
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

/// Whether `t`, under `depth` enclosing binders, has a variable those
/// binders don't bind. The checker's own walk, sharing nothing with the
/// specialiser's `has_free`.
fn has_free_var(s: &TermStore, t: Hash, depth: u32, memo: &mut HashMap<(Hash, u32), bool>) -> bool {
    if let Some(&r) = memo.get(&(t, depth)) {
        return r;
    }
    let term = s.resolve(t);
    let r = match *term {
        Term::Var(i) => i >= depth,
        Term::Abs(b) | Term::Rec(b) => has_free_var(s, b, depth + 1, memo),
        _ => children(term).into_iter().any(|c| has_free_var(s, c, depth, memo)),
    };
    memo.insert((t, depth), r);
    r
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
mod tests;
