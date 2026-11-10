use super::*;

/// `def_eq` answers syntactically equal sides without normalising
/// them (`docs/related-work/` §56). `d (d (... (d x)))` with
/// `d = \x. x x` has a normal form of 2^n nodes, so normalising both
/// sides and comparing takes about 0.3 s at n = 14.
#[test]
fn def_eq_answers_equal_sides_without_normalising() {
    assert_scales("def_eq equal sides", 7, 14, 2, 0, |n| {
        let (a, b) = (doubling(n), doubling(n));
        worked(|| assert!(def_eq(&a, &b)))
    });
}

/// `def_eq` compares weak head normal forms and recurses into the
/// children, so a part both sides share is never normalised
/// (`docs/related-work/` §57). Here the domains are equal copies of §56's
/// doubling term and only the codomains need reducing.
#[test]
fn def_eq_normalises_only_where_the_sides_differ() {
    assert_scales("def_eq shared domains", 7, 14, 2, 0, |n| {
        let a = pi(doubling(n), app(lam(sort(1), var(0)), sort(0)));
        let (b, c) = (pi(doubling(n), sort(0)), pi(doubling(n), sort(1)));
        worked(|| {
            assert!(def_eq(&a, &b));
            assert!(!def_eq(&a, &c));
        })
    });
}

/// `def_eq` decides exactly `nf(a) == nf(b)`: on random terms, some
/// pairs unrelated and some the same term with different redexes
/// inserted.
#[test]
fn def_eq_agrees_with_comparing_normal_forms() {
    let (mut seed, mut equal, mut unequal) = (tatic_rng::SplitMix64::new(7), 0, 0);
    for i in 0..20_000 {
        let a = random_expr(&mut seed, 4);
        let b = if i % 2 == 0 { a } else { random_expr(&mut seed, 4) };
        let (a, b) = (with_redexes(&a, &mut seed), with_redexes(&b, &mut seed));
        let reference = nf(&a) == nf(&b);
        assert_eq!(def_eq(&a, &b), reference, "a {a:?}, b {b:?}");
        if reference && a != b { equal += 1 } else if !reference { unequal += 1 }
    }
    assert!(equal > 2_000 && unequal > 2_000, "equal {equal}, unequal {unequal}");
}

/// `whnf` keeps the node of a stuck head or target, not only of
/// the arguments: the memos are keyed by node, and a copy used to
/// miss them, so each level of a stuck spine then reduced the whole
/// spine below it again (`docs/related-work/` §59).
#[test]
fn whnf_keeps_the_stuck_part_it_was_given() {
    let stuck = app(app(var(0), var(1)), var(2));
    let r = whnf(&app(stuck, var(3)));
    let Node::App(got, _) = r.node() else { panic!("not an application") };
    assert!(node_key(&got) == node_key(&stuck));

    let j = jelim(var(0), var(1), var(2), var(2), stuck);
    let r = whnf(&j);
    let Node::J { p: got, .. } = r.node() else { panic!("not a J") };
    assert!(node_key(&got) == node_key(&stuck));

    let w = wrec(var(0), var(1), var(2), stuck);
    let r = whnf(&w);
    let Node::WRec { target: got, .. } = r.node() else { panic!("not a WRec") };
    assert!(node_key(&got) == node_key(&stuck));

    let s = sigrec(var(0), var(1), stuck);
    let r = whnf(&s);
    let Node::SigRec { target: got, .. } = r.node() else { panic!("not a SigRec") };
    assert!(node_key(&got) == node_key(&stuck));
}

/// `nf` and `def_eq` on stuck spines 16,000 applications deep, one of
/// them with a redex for its head. At 2,000 each took over 10 s in a
/// debug build when every level re-reduced the spine below it
/// (`docs/related-work/` §59), and 0.7 s when every level walked it
/// (§79). Timed against spines a sixteenth as deep: 17-35x in a debug
/// build now, 256x if quadratic. Below about 1,000 the spines stay in
/// cache and the ratio overstates the growth. At an eighth, a quadratic
/// kernel measured 41-65x against a bound of 30 and passed one run in
/// six under load. Every run gets fresh variables so no memo
/// carries over.
#[test]
fn nf_and_def_eq_are_linear_on_a_stuck_spine() {
    let fresh = std::cell::Cell::new(0);
    assert_scales("stuck spine", 1000, 16000, 24, 0, move |depth| {
        let v = fresh.get();
        fresh.set(v + 3);
        let spine = |head: Expr| (0..depth).fold(head, |t, i| app(t, var(v + i % 3)));
        let (a, b, nf_b) = (spine(var(v)), spine(app(lam(sort(0), var(0)), var(v + 1))), spine(var(v + 1)));
        worked(|| {
            assert_eq!(nf(&a), a);
            assert_eq!(nf(&b), nf_b);
            assert!(!def_eq(&a, &b));
        })
    });
}

/// Conversion has no eta: `refl f` proves `Id(A -> B, f, f)` but not
/// `Id(A -> B, f, \x. f x)`, and `def_eq` says the two sides differ.
/// Proofs about machine programs depend on it: a continuation must be
/// passed in exactly the form the machine builds it (`docs/tier-cycle/`,
/// "A store at a run-time address across a call, the cost of `call`, and
/// eta: three follow-ups").
#[test]
fn conversion_has_no_eta() {
    // ctx [A, B, f]: f = var(0), B = var(1), A = var(2)
    let stmt = |rhs: Expr| pi(sort(0), pi(sort(0), pi(arrow(var(1), var(0)), id(arrow(var(2), var(1)), var(0), rhs))));
    let proof = lam(sort(0), lam(sort(0), lam(arrow(var(1), var(0)), refl(var(0)))));
    let eta = lam(var(2), app(var(1), var(0)));
    assert!(check(&Ctx::new(), &proof, &stmt(var(0))).is_ok());
    assert!(check(&Ctx::new(), &proof, &stmt(eta)).is_err());
    let f = var(5);
    assert!(!def_eq(&f, &lam(sort(0), app(shift(&f, 0, 1), var(0)))));
}

