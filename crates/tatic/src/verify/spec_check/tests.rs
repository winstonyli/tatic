use super::*;
use crate::lang::term::PrimOp;

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
fn accepts_beta_v_with_a_bound_variable_argument() {
    // \w. (\x. x + 1) w  ->  \w. w + 1. The redex's argument is free in
    // the redex but bound by \w in the source.
    let mut s = TermStore::new();
    let (v0, one) = (s.var(0), s.lit(1));
    let body = s.prim(PrimOp::Add, v0, one);
    let lam = s.abs(body);
    let r = s.app(lam, v0);
    let h = s.abs(r);
    let want = s.abs(body);
    assert_eq!(one_step(&s, h, r, want), Ok(()));
}

#[test]
fn rejects_an_open_source() {
    // (\x. x + 1) v3, with v3 unbound: `eval` gives UnboundVariable, so
    // v3 is not a value, and (\x. 0) v3 -> 0 would remove an error.
    let mut s = TermStore::new();
    let (x, one, v3) = (s.var(0), s.lit(1), s.var(3));
    let body = s.prim(PrimOp::Add, x, one);
    let lam = s.abs(body);
    let r = s.app(lam, v3);
    let want = s.prim(PrimOp::Add, v3, one);
    let err = one_step(&s, r, r, want).unwrap_err();
    assert_eq!((err.step, err.reason), (0, "source term has free variables"));
    // Under a binder too: \n. (\x. 0) v5, where v5 is Var(4) at top level.
    let (zero, v5) = (s.lit(0), s.var(5));
    let k0 = s.abs(zero);
    let r = s.app(k0, v5);
    let h = s.abs(r);
    let want = s.abs(zero);
    assert_eq!(one_step(&s, h, r, want).unwrap_err().reason, "source term has free variables");
    // Even an empty trace: the check is about the source.
    assert_eq!(check(&s, v3, &[], v3).unwrap_err().reason, "source term has free variables");
}

#[test]
fn accepts_a_capturing_lambda_substituted_under_a_binder() {
    // \w. (\g. \z. g z) (\y. y + w)  ->  \w. \z. (\y. y + w) z
    // Inside the argument's \y, w is Var(1). Under the new \z it is Var(2).
    let mut s = TermStore::new();
    let (v0, v1, v2) = (s.var(0), s.var(1), s.var(2));
    let gz = s.app(v1, v0);
    let inner = s.abs(gz);
    let caller = s.abs(inner);
    let arg_body = s.prim(PrimOp::Add, v0, v1);
    let arg = s.abs(arg_body);
    let r = s.app(caller, arg);
    let h = s.abs(r);
    let want_arg_body = s.prim(PrimOp::Add, v0, v2);
    let want_arg = s.abs(want_arg_body);
    let want_app = s.app(want_arg, v0);
    let want_z = s.abs(want_app);
    let want = s.abs(want_z);
    assert_eq!(one_step(&s, h, r, want), Ok(()));
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
    crate::testing::independence::assert_independent("spec_check.rs", include_str!("../spec_check.rs"), &["specialise", "compile", "lower_wat"], &["lang::term"]);
}

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
    // How many mutants of each kind `check` accepted. For kinds 2 and
    // 3 that is allowed, but only when a second, independent replay
    // (`specialise::replay`, which never calls into this file)
    // confirms the mutant genuinely reaches the claim -- `check`
    // accepting is not itself proof of that, which is exactly the bug
    // a prior version of this test had (it compared the *original*,
    // unmutated trace against the claim, which is true by
    // construction and so could never fail).
    let mut tolerated = [0usize; 5];
    for (name, s, h) in crate::support::samples::corpus() {
        let sp = crate::jit::specialise::specialise(&s, h);
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
        // so acceptance is allowed, but only if an independent replay
        // of the swapped trace itself reaches the claim.
        for i in 0..t.len().saturating_sub(1) {
            let mut m = t.clone();
            m.swap(i, i + 1);
            if m != *t && check(&s, h, &m, sp.term).is_ok() {
                tolerated[1] += 1;
                assert_eq!(
                    crate::jit::specialise::replay(&s, h, &m).map(|(_, r)| r),
                    Some(sp.term),
                    "{name}: swap {i} was accepted by check, but an independent replay of the swapped trace does not confirm it reaches the claim"
                );
            }
            counts[1] += 1;
        }
        // 3. Retarget a step to another subterm of the source. A
        // retargeted step could in principle hit a different valid
        // redex and still reach the same claim (observed on the
        // corpus: over_application_pap_producing_root), so acceptance
        // is allowed, but only if an independent replay of the
        // retargeted trace itself reaches the claim.
        let subs = subterms(&s, h);
        for i in 0..t.len() {
            let Step::BetaV { redex } = t[i];
            for &other in subs.iter().filter(|&&u| u != redex).take(8) {
                let mut m = t.clone();
                m[i] = Step::BetaV { redex: other };
                if check(&s, h, &m, sp.term).is_ok() {
                    tolerated[2] += 1;
                    assert_eq!(
                        crate::jit::specialise::replay(&s, h, &m).map(|(_, r)| r),
                        Some(sp.term),
                        "{name}: retargeting step {i} was accepted by check, but an independent replay of the retargeted trace does not confirm it reaches the claim"
                    );
                }
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
    eprintln!("mutation counts: {counts:?}, tolerated: {tolerated:?}");
    assert!(counts.iter().all(|&c| c > 0), "every mutation kind must run at least once: {counts:?}");
}
