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
///
/// `spec_check::check` rejects a source with more than `MAX_NODES` nodes or
/// with a free variable, whatever the trace, so for such a source this
/// returns the empty trace at once. For any other source, every prefix of
/// a valid trace is itself valid, so stopping early at a limit is safe.
/// The early size test also bounds the work below: every pass rescans the
/// whole term.
pub fn specialise(store: &TermStore, h: Hash) -> Specialised {
    let mut s = TermStore::new();
    // `size` stops counting past MAX_NODES, so this test is cheap even for
    // a huge source. The import is still needed, because `Specialised`
    // owns a store holding `term`; it is linear, unlike the passes.
    let reducible_source = size(store, h) <= MAX_NODES && !has_free(store, h, 0, &mut HashMap::new());
    let mut cur = import(store, &mut s, h, &mut HashMap::new());
    let mut trace = Vec::new();
    if !reducible_source {
        return Specialised { store: s, term: cur, trace };
    }
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
    // `seen` skips a `(hash, in_fn_pos)` already visited. That is right only
    // because hashes are content hashes: an equal hash is an equal
    // subterm, whose first visit already returned `None` (a `Some` would
    // have ended the search). `memos` is shared by every `reducible` call
    // in this pass for the same reason: `s` doesn't change during it.
    fn go(s: &TermStore, t: Hash, in_fn_pos: bool, seen: &mut HashSet<(Hash, bool)>, memos: &mut Memos) -> Option<Hash> {
        if !seen.insert((t, in_fn_pos)) {
            return None;
        }
        match *s.resolve(t) {
            Term::Var(_) | Term::Lit(_) => None,
            Term::Prim(_, a, b) => go(s, a, false, seen, memos).or_else(|| go(s, b, false, seen, memos)),
            Term::If(c, x, y) => go(s, c, false, seen, memos)
                .or_else(|| go(s, x, false, seen, memos))
                .or_else(|| go(s, y, false, seen, memos)),
            Term::Abs(b) | Term::Rec(b) => go(s, b, false, seen, memos),
            Term::App(f, a) => go(s, a, false, seen, memos)
                .or_else(|| go(s, f, true, seen, memos))
                .or_else(|| (!in_fn_pos && reducible(s, t, memos)).then_some(t)),
        }
    }
    go(s, t, false, &mut HashSet::new(), &mut Memos::default())
}

/// `occurrences` and `has_free` memos. Both are pure functions of their
/// memo keys, so one pair serves every argument of every spine in a pass.
#[derive(Default)]
struct Memos {
    occurrences: HashMap<(Hash, u32, bool), (usize, bool)>,
    has_free: HashMap<(Hash, u32), bool>,
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
fn reducible(s: &TermStore, spine: Hash, memos: &mut Memos) -> bool {
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
            let (n, under) = occurrences(s, body, param, false, &mut memos.occurrences);
            !has_free(s, a, 0, &mut memos.has_free) || n == 0 || (n == 1 && !under)
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

/// A second, independent replay of `trace` from `h`, using the
/// specialiser's own substitution (`import`, `instantiate`, `replace`) --
/// never `spec_check`'s. Used only as `spec_check.rs`'s mutation test's
/// oracle: `check` accepting a mutated trace is not, by itself, proof the
/// mutant reaches the claim by anything other than an accident of the
/// checker; this gives the test a way to confirm the claim independently.
/// `None` if any step fails to replay (the redex is absent, isn't
/// `App(Abs(_), _)`, or its argument isn't a value).
#[cfg(test)]
pub(crate) fn replay(store: &TermStore, h: Hash, trace: &[Step]) -> Option<(TermStore, Hash)> {
    fn contains(s: &TermStore, t: Hash, target: Hash) -> bool {
        if t == target {
            return true;
        }
        match *s.resolve(t) {
            Term::Var(_) | Term::Lit(_) => false,
            Term::Prim(_, a, b) | Term::App(a, b) => contains(s, a, target) || contains(s, b, target),
            Term::If(c, x, y) => contains(s, c, target) || contains(s, x, target) || contains(s, y, target),
            Term::Abs(b) | Term::Rec(b) => contains(s, b, target),
        }
    }
    let mut s = TermStore::new();
    let mut cur = import(store, &mut s, h, &mut HashMap::new());
    for &Step::BetaV { redex } in trace {
        if !contains(&s, cur, redex) {
            return None;
        }
        let &Term::App(f, a) = s.resolve(redex) else { return None };
        let &Term::Abs(body) = s.resolve(f) else { return None };
        if !matches!(s.resolve(a), Term::Var(_) | Term::Lit(_) | Term::Abs(_) | Term::Rec(_)) {
            return None;
        }
        let contracted = instantiate(&mut s, body, a);
        cur = replace(&mut s, cur, redex, contracted, &mut HashMap::new());
    }
    Some((s, cur))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::spec_check::check;
    use crate::term::PrimOp;

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
        // Substituting the closed `g` turns `g n` from App(Var, Var)
        // (non-reducible: the head is a variable) into App(Abs(y+1), n),
        // a fresh, policy-legal redex (the argument is a Var) that the next
        // outer-loop pass reduces to `n+1`. Two steps, not one: the
        // checker (an independent implementation) accepts the full
        // 2-step trace via `specialise_checked` above, so this is a real
        // cascading reduction, not a bug.
        let mut s = TermStore::new();
        let h = loop_using(&mut s, false);
        let sp = specialise_checked(&s, h);
        assert_eq!(sp.trace.len(), 2, "{:?}", sp.trace);
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
    fn an_oversized_source_gets_the_empty_trace() {
        let mut s = TermStore::new();
        let h = crate::test_corpus::oversized_source_with_a_shrinking_step(&mut s);
        assert_eq!(check(&s, h, &[], h).unwrap_err().reason, "source term larger than MAX_NODES");
        let sp = specialise(&s, h);
        assert!(sp.trace.is_empty(), "{:?}", sp.trace);
        assert_eq!(sp.term, h);
    }

    #[test]
    fn an_open_source_gets_the_empty_trace() {
        // \n. if n == 777 then (\x. 0) v5 else 1: v5 is unbound, so the
        // redex is not βv and `eval` fails at n = 777.
        let mut s = TermStore::new();
        let h = crate::test_corpus::open_redex_probe(&mut s);
        let sp = specialise(&s, h);
        assert!(sp.trace.is_empty(), "{:?}", sp.trace);
        assert_eq!(sp.term, h);
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
}
