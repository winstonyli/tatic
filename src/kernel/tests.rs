use super::*;

/// Replace `Var(j)` with `s` throughout `e`: the reference `subst_top`
/// is checked against, as `shift(&subst(body, 0, &shift(s, 0, 1)), 0, -1)`.
fn subst(e: &Expr, j: u32, s: &Expr) -> Expr {
    grow(|| match e {
        Expr::Var(k) => {
            if *k == j {
                s.clone()
            } else {
                Expr::Var(*k)
            }
        }
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Const(l) => Expr::Const(*l),
        Expr::Free(l) => Expr::Free(*l),
        Expr::Pi(a, b) => pi(subst(a, j, s), subst(b, j + 1, &shift(s, 0, 1))),
        Expr::Lam(a, b) => lam(subst(a, j, s), subst(b, j + 1, &shift(s, 0, 1))),
        Expr::App(f, a) => app(subst(f, j, s), subst(a, j, s)),
        Expr::Id(a, x, y) => id(subst(a, j, s), subst(x, j, s), subst(y, j, s)),
        Expr::Refl(a) => refl(subst(a, j, s)),
        Expr::J {
            motive,
            base,
            a,
            b,
            p,
        } => jelim(
            subst(motive, j, s),
            subst(base, j, s),
            subst(a, j, s),
            subst(b, j, s),
            subst(p, j, s),
        ),
        Expr::W(a, b) => wty(subst(a, j, s), subst(b, j + 1, &shift(s, 0, 1))),
        Expr::Sup(a, f) => sup(subst(a, j, s), subst(f, j, s)),
        Expr::WRec {
            motive,
            children_ty,
            step,
            target,
        } => wrec(subst(motive, j, s), subst(children_ty, j + 1, &shift(s, 0, 1)), subst(step, j, s), subst(target, j, s)),
        Expr::Sigma(..) | Expr::Pair(..) | Expr::SigRec { .. } => subst_sigma_family(e, j, s),
    })
}

/// `subst`'s own `Sigma`/`Pair`/`SigRec` cases, out of line -- see
/// `shift_sigma_family`'s own docs for why.
#[inline(never)]
fn subst_sigma_family(e: &Expr, j: u32, s: &Expr) -> Expr {
    match e {
        Expr::Sigma(a, b) => sigma(subst(a, j, s), subst(b, j + 1, &shift(s, 0, 1))),
        Expr::Pair(fam, a, b) => pair(subst(fam, j + 1, &shift(s, 0, 1)), subst(a, j, s), subst(b, j, s)),
        Expr::SigRec { motive, step, target } => sigrec(subst(motive, j, s), subst(step, j, s), subst(target, j, s)),
        _ => unreachable!("subst_sigma_family called on a non-Sigma-family Expr"),
    }
}

/// A splitmix64 stream, for the randomised tests below.
fn splitmix(mut seed: u64) -> impl FnMut() -> usize {
    move || {
        seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = seed;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        (z ^ (z >> 31)) as usize
    }
}

/// A random term with every `Expr` shape, built from a pool of nodes so
/// children are shared. Its leaves are `Var(0..4)`, `Sort(0)`,
/// `Const(0)`, `Const(1)`, `Free(0)` and `Free(2)`, so it has both open
/// and closed subterms at every binder depth, and terms with and
/// without a `Free`.
fn random_term(next: &mut impl FnMut() -> usize) -> Expr {
    let mut pool: Vec<Rc<Expr>> = (0..4)
        .map(|k| Rc::new(var(k)))
        .chain([Rc::new(sort(0)), Rc::new(Expr::Const(0)), Rc::new(Expr::Const(1)), Rc::new(Expr::Free(0)), Rc::new(Expr::Free(2))])
        .collect();
    for _ in 0..12 {
        let kind = next() % 14;
        let mut c = || pool[next() % pool.len()].clone();
        let node = match kind {
            0 => Expr::Pi(c(), c()),
            1 => Expr::Lam(c(), c()),
            2 | 3 => Expr::App(c(), c()),
            4 => Expr::Id(c(), c(), c()),
            5 => Expr::Refl(c()),
            6 => Expr::J { motive: c(), base: c(), a: c(), b: c(), p: c() },
            7 => Expr::W(c(), c()),
            8 => Expr::Sup(c(), c()),
            9 => Expr::WRec { motive: c(), children_ty: c(), step: c(), target: c() },
            10 => Expr::Sigma(c(), c()),
            11 => Expr::Pair(c(), c(), c()),
            12 => Expr::SigRec { motive: c(), step: c(), target: c() },
            _ => Expr::Sort(1),
        };
        pool.push(Rc::new(node));
    }
    (**pool.last().unwrap()).clone()
}

/// The pre-§64 `is_var_free`, kept as the reference for the new one and for
/// `loose_of`. It walks the whole term and reads no cached range.
fn is_var_free_ref(e: &Expr, idx: u32) -> bool {
    let f = is_var_free_ref;
    grow(|| match e {
        Expr::Var(k) => *k == idx,
        Expr::Sort(_) | Expr::Const(_) | Expr::Free(_) => false,
        Expr::Pi(a, b) | Expr::Lam(a, b) | Expr::W(a, b) | Expr::Sigma(a, b) => f(a, idx) || f(b, idx + 1),
        Expr::App(a, b) | Expr::Sup(a, b) => f(a, idx) || f(b, idx),
        Expr::Id(a, x, y) => f(a, idx) || f(x, idx) || f(y, idx),
        Expr::Refl(a) => f(a, idx),
        Expr::J { motive, base, a, b, p } => f(motive, idx) || f(base, idx) || f(a, idx) || f(b, idx) || f(p, idx),
        Expr::WRec { motive, children_ty, step, target } => {
            f(motive, idx) || f(children_ty, idx + 1) || f(step, idx) || f(target, idx)
        }
        Expr::Pair(fam, a, b) => f(fam, idx + 1) || f(a, idx) || f(b, idx),
        Expr::SigRec { motive, step, target } => f(motive, idx) || f(step, idx) || f(target, idx),
    })
}

/// The pre-§64 `shift`, kept as the reference for the new one. It rebuilds
/// every node, so it's also a deep copy that shares nothing.
fn shift_ref(e: &Expr, cutoff: u32, amount: i32) -> Expr {
    let go = |x: &Rc<Expr>, c: u32| shift_ref(x, c, amount);
    grow(|| match e {
        Expr::Var(k) => {
            if *k >= cutoff {
                Expr::Var((*k as i32 + amount) as u32)
            } else {
                Expr::Var(*k)
            }
        }
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Const(l) => Expr::Const(*l),
        Expr::Free(l) => Expr::Free(*l),
        Expr::Pi(a, b) => pi(go(a, cutoff), go(b, cutoff + 1)),
        Expr::Lam(a, b) => lam(go(a, cutoff), go(b, cutoff + 1)),
        Expr::App(f, a) => app(go(f, cutoff), go(a, cutoff)),
        Expr::Id(a, x, y) => id(go(a, cutoff), go(x, cutoff), go(y, cutoff)),
        Expr::Refl(a) => refl(go(a, cutoff)),
        Expr::J { motive, base, a, b, p } => {
            jelim(go(motive, cutoff), go(base, cutoff), go(a, cutoff), go(b, cutoff), go(p, cutoff))
        }
        Expr::W(a, b) => wty(go(a, cutoff), go(b, cutoff + 1)),
        Expr::Sup(a, f) => sup(go(a, cutoff), go(f, cutoff)),
        Expr::WRec { motive, children_ty, step, target } => {
            wrec(go(motive, cutoff), go(children_ty, cutoff + 1), go(step, cutoff), go(target, cutoff))
        }
        Expr::Sigma(a, b) => sigma(go(a, cutoff), go(b, cutoff + 1)),
        Expr::Pair(fam, a, b) => pair(go(fam, cutoff + 1), go(a, cutoff), go(b, cutoff)),
        Expr::SigRec { motive, step, target } => sigrec(go(motive, cutoff), go(step, cutoff), go(target, cutoff)),
    })
}

/// The pre-§64 `instantiate`, kept as the reference for the new one.
fn instantiate_ref(e: &Expr, s: &Expr, d: u32) -> Expr {
    let go = |x: &Rc<Expr>, d: u32| instantiate_ref(x, s, d);
    grow(|| match e {
        Expr::Var(k) => {
            if *k == d {
                shift_ref(s, 0, d as i32)
            } else if *k > d {
                Expr::Var(*k - 1)
            } else {
                Expr::Var(*k)
            }
        }
        Expr::Sort(i) => Expr::Sort(*i),
        Expr::Const(l) => Expr::Const(*l),
        Expr::Free(l) => Expr::Free(*l),
        Expr::Pi(a, b) => pi(go(a, d), go(b, d + 1)),
        Expr::Lam(a, b) => lam(go(a, d), go(b, d + 1)),
        Expr::App(f, a) => app(go(f, d), go(a, d)),
        Expr::Id(a, x, y) => id(go(a, d), go(x, d), go(y, d)),
        Expr::Refl(a) => refl(go(a, d)),
        Expr::J { motive, base, a, b, p } => jelim(go(motive, d), go(base, d), go(a, d), go(b, d), go(p, d)),
        Expr::W(a, b) => wty(go(a, d), go(b, d + 1)),
        Expr::Sup(a, f) => sup(go(a, d), go(f, d)),
        Expr::WRec { motive, children_ty, step, target } => wrec(go(motive, d), go(children_ty, d + 1), go(step, d), go(target, d)),
        Expr::Sigma(a, b) => sigma(go(a, d), go(b, d + 1)),
        Expr::Pair(fam, a, b) => pair(go(fam, d + 1), go(a, d), go(b, d)),
        Expr::SigRec { motive, step, target } => sigrec(go(motive, d), go(step, d), go(target, d)),
    })
}

/// A term's cached range is one more than its largest free variable,
/// as a walk of the whole term finds it (0 when closed). The
/// pool's variables are below 4 and binders only lower them, so
/// checking indices below 8 covers every one that can occur.
/// A DAG whose tree is 2^60 nodes prints as about 400 characters, at once (doc section 82).
#[test]
fn brief_bounds_the_text_of_an_exponential_tree() {
    let mut e = sort(0);
    for _ in 0..60 {
        let shared = Rc::new(e);
        e = Expr::App(shared.clone(), shared);
    }
    let t = std::time::Instant::now();
    let text = brief(&e);
    assert!(text.len() <= 400 + 4, "{} chars", text.len());
    assert!(text.ends_with(" ..."));
    assert!(t.elapsed() < std::time::Duration::from_millis(100), "took {:?}", t.elapsed());
    assert_eq!(brief(&sort(3)), "Type3");
}

#[test]
fn loose_matches_a_walk() {
    let mut next = splitmix(11);
    for _ in 0..20_000 {
        let e = random_term(&mut next);
        let walk = (0..8u32).rev().find(|&i| is_var_free_ref(&e, i)).map_or(0, |i| i + 1);
        assert_eq!(Rc::new(e.clone()).loose(), walk, "{e:?}");
    }
}

/// The new `shift`, `instantiate` and `is_var_free` agree with today's
/// on random terms, at several cutoffs and depths, and a shift up and
/// back down is the identity.
#[test]
fn shift_and_instantiate_match_a_reference() {
    let mut next = splitmix(23);
    for _ in 0..20_000 {
        let e = random_term(&mut next);
        let s = random_term(&mut next);
        for c in 0..4 {
            for n in [1, 2] {
                assert_eq!(shift(&e, c, n), shift_ref(&e, c, n), "shift({e:?}, {c}, {n})");
            }
            // Shifting down by 1 at `c` is defined when `Var(c)` isn't
            // free: always after a shift up, and on `e` when it lacks it.
            let up = shift_ref(&e, c, 1);
            assert_eq!(shift(&up, c, -1), shift_ref(&up, c, -1), "shift({up:?}, {c}, -1)");
            if !is_var_free_ref(&e, c) {
                assert_eq!(shift(&e, c, -1), shift_ref(&e, c, -1), "shift({e:?}, {c}, -1)");
            }
            assert_eq!(shift(&shift(&e, c, 1), c, -1), e, "shift back ({e:?}, {c})");
            assert_eq!(instantiate(&e, &s, c), instantiate_ref(&e, &s, c), "instantiate({e:?}, {s:?}, {c})");
        }
        for i in 0..6 {
            assert_eq!(is_var_free(&e, i), is_var_free_ref(&e, i), "is_var_free({e:?}, {i})");
        }
    }
}

/// `shift_memo` equals `shift` on random terms, with one memo shared across terms, cutoffs and
/// amounts (so entries are reused and must be keyed by all three).
#[test]
fn shift_memo_matches_shift() {
    let mut next = splitmix(57);
    let memo = ShiftMemo::default();
    for _ in 0..20_000 {
        let e = random_term(&mut next);
        for c in 0..4 {
            for n in [1, 2, 3] {
                assert_eq!(shift_memo(&e, c, n, &memo), shift(&e, c, n), "shift_memo({e:?}, {c}, {n})");
            }
        }
    }
}

/// `instantiate_n` equals one `subst_top` per argument, outermost first, on random terms.
#[test]
fn instantiate_n_matches_sequential_substitution() {
    let mut next = splitmix(41);
    for _ in 0..20_000 {
        let e = random_term(&mut next);
        let m = 1 + (next() % 3);
        let args: Vec<Expr> = (0..m).map(|_| random_term(&mut next)).collect();
        // `lam^m(e)` applied to `args`, one beta at a time
        let mut body = e.clone();
        for _ in 1..m {
            body = lam(sort(0), body);
        }
        let mut cur = body;
        for (i, a) in args.iter().enumerate() {
            let next_body = instantiate_ref(&cur, a, 0);
            cur = if i + 1 < m {
                match &next_body {
                    Expr::Lam(_, b) => (**b).clone(),
                    other => panic!("lost the inner lambda: {other:?}"),
                }
            } else {
                next_body
            };
        }
        let refs: Vec<&Expr> = args.iter().collect();
        assert_eq!(instantiate_n(&e, &refs, 0), cur, "e {e:?}, args {args:?}");
    }
}

/// A child with nothing to change comes back as the same `Rc`, not a
/// copy: a closed one always, and an open one when its variables are
/// all below the cutoff or depth.
#[test]
fn shift_keeps_closed_children_by_pointer() {
    // `Expr` has a custom `Drop` (the deep-drop guard), so it can't be
    // destructured by move; each result is matched by reference instead.
    let closed = Rc::new(pi(sort(0), var(0)));
    let e = Expr::App(closed.clone(), Rc::new(var(0)));
    let shifted = shift(&e, 0, 1);
    let Expr::App(f, a) = &shifted else { panic!() };
    assert!(Rc::ptr_eq(f, &closed), "shift copied a closed child");
    assert_eq!(**a, var(1));
    let instantiated = instantiate(&e, &sort(1), 0);
    let Expr::App(f, a) = &instantiated else { panic!() };
    assert!(Rc::ptr_eq(f, &closed), "instantiate copied a closed child");
    assert_eq!(**a, sort(1));

    // Under cutoff 1, `Var(0)` is bound, so its child keeps its pointer
    // and only `Var(2)` moves.
    let low = Rc::new(var(0));
    let e = Expr::App(low.clone(), Rc::new(var(2)));
    let shifted = shift(&e, 1, 1);
    let Expr::App(f, a) = &shifted else { panic!() };
    assert!(Rc::ptr_eq(f, &low), "shift copied a child below the cutoff");
    assert_eq!(**a, var(3));
    let instantiated = instantiate(&e, &sort(1), 1);
    let Expr::App(f, a) = &instantiated else { panic!() };
    assert!(Rc::ptr_eq(f, &low), "instantiate copied a child below the depth");
    assert_eq!(**a, var(1));

    // A whole term with nothing to change comes back with its children
    // by pointer; check the domain.
    let e = Expr::Pi(closed.clone(), Rc::new(var(0)));
    let shifted = shift(&e, 0, 5);
    let Expr::Pi(dom, _) = &shifted else { panic!() };
    assert!(Rc::ptr_eq(dom, &closed));
}

/// The largest `Free` level a walk of the whole term finds, plus one
/// (0 with none): the reference for the cached `free` range.
fn free_ref(e: &Expr) -> u32 {
    grow(|| match e {
        Expr::Free(l) => l + 1,
        _ => {
            let mut m = 0;
            same_shape(e, e, |c, _| {
                m = m.max(free_ref(c));
                true
            });
            m
        }
    })
}

/// Every node's cached `free` range is the one a walk finds, and a
/// binder doesn't lower it (a `Free` is a level, not an index).
#[test]
fn free_matches_a_walk() {
    let mut next = splitmix(31);
    let mut with_free = 0;
    for _ in 0..20_000 {
        let e = random_term(&mut next);
        let walk = free_ref(&e);
        with_free += (walk > 0) as usize;
        assert_eq!(Rc::new(e.clone()).free(), walk, "{e:?}");
        assert_eq!(free_of(&e), walk, "{e:?}");
    }
    assert!(with_free > 2_000, "only {with_free} terms had a Free");
}

/// The two new leaves are neutral atoms: each is equal only to itself,
/// and never to the other kind or to a `Var` with the same number.
#[test]
fn const_and_free_are_equal_only_to_themselves() {
    let (c0, c1, f0, f1) = (Expr::Const(0), Expr::Const(1), Expr::Free(0), Expr::Free(1));
    assert!(def_eq(&c0, &Expr::Const(0)));
    assert!(def_eq(&f0, &Expr::Free(0)));
    for (x, y) in [(&c0, &c1), (&f0, &f1), (&c0, &f0), (&c0, &var(0)), (&f0, &var(0))] {
        assert!(!def_eq(x, y), "{x:?} vs {y:?}");
        assert!(x != y, "{x:?} == {y:?}");
    }
}

/// Beta reduction substitutes for the bound `Var` only: a `Const` or a
/// `Free` in the body, or in the argument, comes through unchanged.
#[test]
fn beta_leaves_const_and_free_alone() {
    let body = app(Expr::Const(0), var(0));
    assert_eq!(whnf(&app(lam(sort(0), Expr::Const(0)), sort(0))), Expr::Const(0));
    assert_eq!(whnf(&app(lam(sort(0), body), Expr::Free(3))), app(Expr::Const(0), Expr::Free(3)));
    assert_eq!(nf(&app(lam(sort(0), Expr::Free(1)), var(5))), Expr::Free(1));
}

/// Both ranges fit the padding stage 1 left (`RELATED_WORK.md` §64):
/// a node is a 48-byte `Expr` and two `u32`s.
#[test]
fn a_node_is_56_bytes() {
    assert_eq!(std::mem::size_of::<Expr>(), 48);
    // The `hashcons` generation (a third `u32`) costs a word.
    assert_eq!(std::mem::size_of::<Node<Expr>>(), if cfg!(feature = "hashcons") { 64 } else { 56 });
}

/// A random `Expr` of every variant, ill-typed as often as not, with
/// indices small enough that `Var(0)` is often free and often not.
fn random_expr(seed: &mut u64, fuel: u32) -> Expr {
    let mut next = || {
        *seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = *seed;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    };
    let pick = next();
    let k = (next() % 4) as u32;
    if fuel == 0 || pick % 4 == 0 {
        return if pick % 8 == 0 { sort(k % 2) } else { var(k) };
    }
    let mut sub = || random_expr(seed, fuel - 1);
    match (pick >> 3) % 13 {
        0 => pi(sub(), sub()),
        1 => lam(sub(), sub()),
        2 => app(sub(), sub()),
        3 => id(sub(), sub(), sub()),
        4 => refl(sub()),
        5 => jelim(sub(), sub(), sub(), sub(), sub()),
        6 => wty(sub(), sub()),
        7 => sup(sub(), sub()),
        8 => wrec(sub(), sub(), sub(), sub()),
        9 => sigma(sub(), sub()),
        10 => pair(sub(), sub(), sub()),
        11 => sigrec(sub(), sub(), sub()),
        _ => app(sub(), sub()),
    }
}

/// `subst_top`'s one pass (`RELATED_WORK.md` §53) must give exactly
/// what substituting and then shifting gives, both when the body uses
/// the variable and when it doesn't.
#[test]
fn subst_top_is_substituting_then_shifting() {
    let (mut seed, mut used, mut unused) = (1u64, 0, 0);
    for _ in 0..20_000 {
        let body = random_expr(&mut seed, 5);
        let s = random_expr(&mut seed, 3);
        let reference = shift(&subst(&body, 0, &shift(&s, 0, 1)), 0, -1);
        assert_eq!(subst_top(&body, &s), reference, "body {body:?}, s {s:?}");
        if is_var_free(&body, 0) { used += 1 } else { unused += 1 }
    }
    assert!(used > 2_000 && unused > 2_000, "used {used}, unused {unused}");
}

#[test]
fn subst_top_leaves_an_unused_argument_alone() {
    // 21 distinct nodes, a million as a tree: copying it takes about a
    // second in a debug build, and the shortcut doesn't look at it.
    let mut s = var(0);
    for _ in 0..20 {
        s = app(s.clone(), s);
    }
    let body = pi(var(3), var(4));
    let t = std::time::Instant::now();
    assert_eq!(subst_top(&body, &s), pi(var(2), var(3)));
    assert!(t.elapsed() < std::time::Duration::from_millis(50), "took {:?}", t.elapsed());
}

/// Substituting under binders shifts the argument once, where it's used,
/// not again at every binder crossed on the way (`RELATED_WORK.md` §52).
/// Timed against one shift of the argument, so it holds on any machine.
#[test]
fn subst_top_shifts_a_used_argument_once() {
    let mut s = var(0);
    for _ in 0..14 {
        s = app(s.clone(), s);
    }
    let depth = 30;
    let mut body = var(depth);
    let mut expected = shift(&s, 0, depth as i32);
    let t = std::time::Instant::now();
    let one_shift = shift(&s, 0, depth as i32);
    let one_shift_time = t.elapsed();
    drop(one_shift);
    for _ in 0..depth {
        body = lam(sort(0), body);
        expected = lam(sort(0), expected);
    }
    let t = std::time::Instant::now();
    let got = subst_top(&body, &s);
    let took = t.elapsed();
    assert_eq!(got, expected);
    assert!(took < one_shift_time * 4 + std::time::Duration::from_millis(5), "took {took:?}, one shift {one_shift_time:?}");
}

/// `def_eq` answers syntactically equal sides without normalising
/// them (`RELATED_WORK.md` §56). `d (d (... (d x)))` with
/// `d = \x. x x` has a normal form of 2^n nodes, so normalising both
/// sides and comparing takes about 0.3 s at n = 14.
#[test]
fn def_eq_answers_equal_sides_without_normalising() {
    let doubling = || {
        let mut t = var(0);
        for _ in 0..14 {
            t = app(lam(sort(0), app(var(0), var(0))), t);
        }
        t
    };
    let (a, b) = (doubling(), doubling());
    let t = std::time::Instant::now();
    assert!(def_eq(&a, &b));
    let took = t.elapsed();
    assert!(took < std::time::Duration::from_millis(5), "took {took:?}");
}

/// `def_eq` compares weak head normal forms and recurses into the
/// children, so a part both sides share is never normalised
/// (`RELATED_WORK.md` §57). Here the domains are equal copies of §56's
/// doubling term and only the codomains need reducing.
#[test]
fn def_eq_normalises_only_where_the_sides_differ() {
    let doubling = || {
        let mut t = var(0);
        for _ in 0..14 {
            t = app(lam(sort(0), app(var(0), var(0))), t);
        }
        t
    };
    let a = pi(doubling(), app(lam(sort(1), var(0)), sort(0)));
    let b = pi(doubling(), sort(0));
    let t = std::time::Instant::now();
    assert!(def_eq(&a, &b));
    assert!(!def_eq(&a, &pi(doubling(), sort(1))));
    let took = t.elapsed();
    assert!(took < std::time::Duration::from_millis(5), "took {took:?}");
}

/// Wraps some of `e`'s subterms in a redex that reduces back to them,
/// `(\_. x) Sort(0)` with `x` shifted under the new binder.
fn with_redexes(e: &Expr, seed: &mut u64) -> Expr {
    *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    let wrap = (*seed >> 33).is_multiple_of(4);
    let mut go = |x: &Rc<Expr>| with_redexes(x, seed);
    let rebuilt = match e {
        Expr::Pi(a, b) => pi(go(a), go(b)),
        Expr::Lam(a, b) => lam(go(a), go(b)),
        Expr::App(f, a) => app(go(f), go(a)),
        Expr::Id(a, x, y) => id(go(a), go(x), go(y)),
        Expr::Sigma(a, b) => sigma(go(a), go(b)),
        Expr::Pair(fam, a, b) => pair(go(fam), go(a), go(b)),
        other => other.clone(),
    };
    if wrap { app(lam(sort(0), shift(&rebuilt, 0, 1)), sort(0)) } else { rebuilt }
}

/// `def_eq` decides exactly `nf(a) == nf(b)`: on random terms, some
/// pairs unrelated and some the same term with different redexes
/// inserted.
#[test]
fn def_eq_agrees_with_comparing_normal_forms() {
    let (mut seed, mut equal, mut unequal) = (7u64, 0, 0);
    for i in 0..20_000 {
        let a = random_expr(&mut seed, 4);
        let b = if i % 2 == 0 { a.clone() } else { random_expr(&mut seed, 4) };
        let (a, b) = (with_redexes(&a, &mut seed), with_redexes(&b, &mut seed));
        let reference = nf(&a) == nf(&b);
        assert_eq!(def_eq(&a, &b), reference, "a {a:?}, b {b:?}");
        if reference && a != b { equal += 1 } else if !reference { unequal += 1 }
    }
    assert!(equal > 2_000 && unequal > 2_000, "equal {equal}, unequal {unequal}");
}

/// The argument `Rc` of each application in `e`'s spine, outermost
/// first.
fn spine_args(e: &Expr) -> Vec<Rc<Expr>> {
    let mut out = Vec::new();
    let mut e = e;
    while let Expr::App(f, a) = e {
        out.push(a.clone());
        e = f;
    }
    out
}

/// `whnf` keeps the allocation of a stuck head or target, not only of
/// the arguments: `ReductionCache` is keyed by pointer, so a copy
/// misses it, and each level of a stuck spine then reduced the whole
/// spine below it again (`RELATED_WORK.md` §59).
#[test]
fn whnf_keeps_the_stuck_part_it_was_given() {
    let stuck = Rc::new(app(app(var(0), var(1)), var(2)));
    let r = whnf(&Expr::App(stuck.clone(), Rc::new(var(3))));
    let Expr::App(got, _) = &r else { panic!("not an application") };
    assert!(Rc::ptr_eq(got, &stuck));

    let j = Expr::J {
        motive: Rc::new(var(0)),
        base: Rc::new(var(1)),
        a: Rc::new(var(2)),
        b: Rc::new(var(2)),
        p: stuck.clone(),
    };
    let r = whnf(&j);
    let Expr::J { p: got, .. } = &r else { panic!("not a J") };
    assert!(Rc::ptr_eq(got, &stuck));

    let w = Expr::WRec {
        motive: Rc::new(var(0)),
        children_ty: Rc::new(var(1)),
        step: Rc::new(var(2)),
        target: stuck.clone(),
    };
    let r = whnf(&w);
    let Expr::WRec { target: got, .. } = &r else { panic!("not a WRec") };
    assert!(Rc::ptr_eq(got, &stuck));

    let s = Expr::SigRec { motive: Rc::new(var(0)), step: Rc::new(var(1)), target: stuck.clone() };
    let r = whnf(&s);
    let Expr::SigRec { target: got, .. } = &r else { panic!("not a SigRec") };
    assert!(Rc::ptr_eq(got, &stuck));
}

/// `nf` and `def_eq` on stuck spines 2,000 applications deep, one of
/// them with a redex for its head. Each took over 10 s in a debug build
/// when every level re-reduced the spine below it (`RELATED_WORK.md`
/// §59).
#[test]
fn nf_and_def_eq_are_linear_on_a_stuck_spine() {
    let spine = |head: Expr| {
        let mut t = head;
        for i in 0..2000 {
            t = app(t, var(i % 3));
        }
        t
    };
    let (a, b) = (spine(var(0)), spine(app(lam(sort(0), var(0)), var(1))));
    let t = std::time::Instant::now();
    assert_eq!(nf(&a), a);
    assert_eq!(nf(&b), spine(var(1)));
    assert!(!def_eq(&a, &b));
    let took = t.elapsed();
    assert!(took < std::time::Duration::from_millis(500), "took {took:?}");
}

/// `A : Type0, a : A, f : A -> A -> A, g : A -> A`, the context the
/// `infer` memo tests below build terms in. Built by hand as `Var`s
/// (these are exactly the terms `Postulates::get` produced here before
/// postulates became `Const`s) since those tests key their pool of
/// nodes on `var(k)`, not on a `Postulates`.
fn memo_test_ctx() -> Ctx {
    let mut ctx = Ctx::new();
    ctx.push_back(sort(0));
    ctx.push_back(var(0));
    ctx.push_back(arrow(var(1), arrow(var(1), var(1))));
    ctx.push_back(arrow(var(2), var(2)));
    ctx
}

/// `d(k+1) = f d(k) d(k)`, 20 levels deep: a million leaves as a
/// tree, 20 shared nodes as a DAG. Without the memo `infer` walked the
/// tree (`RELATED_WORK.md` §63). Postulates as `Const`s, per stage 3.
#[test]
fn infer_is_linear_in_the_dag_of_a_shared_term() {
    let mut p = Postulates::new();
    let a_ty = p.push(sort(0));
    p.push(p.get(a_ty));
    p.push(arrow(p.get(a_ty), arrow(p.get(a_ty), p.get(a_ty))));
    p.push(arrow(p.get(a_ty), p.get(a_ty)));
    let mut d = Rc::new(p.get(1));
    for _ in 0..20 {
        d = Rc::new(Expr::App(Rc::new(Expr::App(Rc::new(p.get(2)), d.clone())), d));
    }
    let t = std::time::Instant::now();
    assert_eq!(p.infer(&d), Ok(p.get(0)));
    let took = t.elapsed();
    assert!(took < std::time::Duration::from_millis(500), "took {took:?}");
}

/// One node shared under two different binder types has two types.
/// `Pi(Type0, Pi(x, Type0))` is well-typed, `Pi(Type0 -> Type0,
/// Pi(x, Type0))` isn't (`x` is then a function, not a type), and
/// both share the inner `Pi`. A memo keyed on context length would
/// reuse the first's answer for the second and accept.
#[test]
fn infer_memo_keeps_same_length_contexts_apart() {
    let inner = Rc::new(Expr::Pi(Rc::new(var(0)), Rc::new(sort(0))));
    let good = Expr::Pi(Rc::new(sort(0)), inner.clone());
    let bad = Expr::Pi(Rc::new(pi(sort(0), sort(0))), inner);
    assert_eq!(infer(&Ctx::new(), &good), Ok(sort(1)));
    assert!(infer(&Ctx::new(), &id(sort(1), good, bad)).is_err());
}

/// No node in `e` is reachable twice or held elsewhere: every child's
/// count is 1, so `infer`'s memo, which only engages on shared nodes,
/// never does.
fn shares_nothing(e: &Expr) -> bool {
    let mut ok = true;
    same_shape(e, e, |c, _| {
        ok = ok && Rc::strong_count(c) == 1 && shares_nothing(c);
        true
    });
    ok
}

/// Random terms built from a pool of nodes, so children are shared,
/// give the same `infer` result as a copy with no sharing (a full
/// rebuild by `shift_ref`, since `shift` now keeps closed subterms),
/// which the memo never engages on (`RELATED_WORK.md` §63).
#[test]
fn infer_memo_changes_no_answer() {
    let ctx = memo_test_ctx();
    let mut next = splitmix(7);
    let mut typed = 0;
    for _ in 0..100_000 {
        let mut pool: Vec<Rc<Expr>> = (0..4).map(|k| Rc::new(var(k))).chain([Rc::new(sort(0))]).collect();
        for _ in 0..10 {
            let kind = next() % 8;
            let mut c = || pool[next() % pool.len()].clone();
            let node = match kind {
                0..=2 => Expr::App(c(), c()),
                3 => Expr::Lam(c(), c()),
                4 => Expr::Pi(c(), c()),
                5 => Expr::Refl(c()),
                6 => Expr::Id(c(), c(), c()),
                _ => Expr::Sigma(c(), c()),
            };
            pool.push(Rc::new(node));
        }
        let e = (**pool.last().unwrap()).clone();
        let unshared = shift_ref(&shift_ref(&e, 0, 1), 0, -1);
        assert!(shares_nothing(&unshared), "the copy shares a node: {e:?}");
        let got = infer(&ctx, &e);
        typed += got.is_ok() as usize;
        assert_eq!(got, infer(&ctx, &unshared), "{e:?}");
    }
    assert!(typed > 1000, "only {typed} well-typed terms");
}

/// `def_eq` on two right-nested chains `f (f (... x))`, 8,000 deep,
/// that differ only at the bottom. `conv` tries `==` at every level,
/// and each failing `==` walked down to the bottom again: 23 s in a
/// debug build (`RELATED_WORK.md` §61).
#[test]
fn def_eq_is_linear_on_a_chain_that_differs_at_the_bottom() {
    let chain = |bottom: Expr| {
        let mut t = bottom;
        for _ in 0..8000 {
            t = app(var(0), t);
        }
        t
    };
    let (a, b) = (chain(var(1)), chain(var(2)));
    let t = std::time::Instant::now();
    assert!(!def_eq(&a, &b));
    let took = t.elapsed();
    assert!(took < std::time::Duration::from_millis(500), "took {took:?}");
}

/// `whnf` keeps each argument's allocation rather than copying it into
/// a new `Rc`: `ReductionCache` is keyed by pointer, so a copy misses it,
/// and `nf` then normalises the whole argument again at every
/// application (`RELATED_WORK.md` §48).
#[test]
fn whnf_keeps_the_arguments_it_was_given() {
    let x = Rc::new(var(7));
    let y = Rc::new(var(8));
    let same = |got: &[Rc<Expr>], want: &[&Rc<Expr>]| {
        got.len() == want.len() && got.iter().zip(want).all(|(g, w)| Rc::ptr_eq(g, w))
    };

    // A stuck application.
    let stuck = Expr::App(Rc::new(app(var(0), var(1))), x.clone());
    assert!(same(&spine_args(&whnf(&stuck))[..1], &[&x]));

    // `J` on `refl` reduces to `base a`.
    let j = Expr::J {
        motive: Rc::new(var(0)),
        base: Rc::new(var(1)),
        a: x.clone(),
        b: x.clone(),
        p: Rc::new(refl(var(9))),
    };
    assert!(same(&spine_args(&whnf(&j)), &[&x]));

    // `SigRec` on a pair reduces to `step a b`.
    let s = Expr::SigRec {
        motive: Rc::new(var(0)),
        step: Rc::new(var(1)),
        target: Rc::new(Expr::Pair(Rc::new(var(2)), x.clone(), y.clone())),
    };
    assert!(same(&spine_args(&whnf(&s)), &[&y, &x]));

    // `WRec` on `sup a f` reduces to `step a f rec`.
    let w = Expr::WRec {
        motive: Rc::new(var(0)),
        children_ty: Rc::new(var(1)),
        step: Rc::new(var(2)),
        target: Rc::new(Expr::Sup(x.clone(), y.clone())),
    };
    assert!(same(&spine_args(&whnf(&w))[1..], &[&y, &x]));
}

/// Every recursive traversal `check` reaches -- `infer`, `whnf`
/// (beta-reducing the whole chain), `def_eq`'s `conv` and `==`, and
/// `Debug` in the error message -- must survive a term 1,000 levels
/// deep on a 1 MB thread: the Windows main thread's size, where a debug
/// build used to overflow at depth ~90 (`RELATED_WORK.md` 31). Goes
/// through `check`, which has no depth guard, on purpose.
#[test]
fn check_survives_a_term_far_deeper_than_the_native_stack_allows() {
    const N: usize = 1_000;
    std::thread::Builder::new()
        .stack_size(1 << 20)
        .spawn(|| {
            let ctx = Ctx::new();

            // (\x:Type0. x) applied N-fold to Type0 -- infer + beta.
            let id_fn = lam(sort(1), var(0));
            let mut chain = sort(0);
            for _ in 0..N {
                chain = app(id_fn.clone(), chain);
            }
            assert!(check(&ctx, &chain, &sort(1)).is_ok());

            // refl^N(Type0) against its own type, built independently,
            // so def_eq's `==` walks two distinct deep trees.
            let (mut e, mut ty) = (sort(0), sort(1));
            for _ in 0..N {
                ty = id(ty, e.clone(), e.clone());
                e = refl(e);
            }
            assert!(check(&ctx, &e, &ty).is_ok());
            let err = check(&ctx, &e, &sort(0)).unwrap_err();
            assert!(err.contains("type mismatch"), "unexpected error: {}", err.chars().take(80).collect::<String>());
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Guards `Drop for Expr`'s swap-onto-a-fresh-segment path specifically
/// (`RELATED_WORK.md` §64 / spec Risks): freeing an unshared child needs
/// the kernel `Rc`'s `strong_count` to reach the inner `std::rc::Rc`'s
/// count exactly, or that path never fires and every child is dropped
/// by plain recursive field-drop glue instead. `check_survives_*` above
/// can't catch a broken `strong_count` here -- 1,000 levels of `Drop`'s
/// own small per-level frame (a match plus a couple of closure calls)
/// fit in a 1 MB stack even with no protection at all, unlike
/// `infer`/`check`/`whnf`'s much heavier frames. This builds a much
/// deeper, wholly unshared chain and only drops it, so it fails however
/// the protection breaks.
#[test]
fn dropping_a_deep_term_does_not_overflow_the_stack() {
    const N: usize = 100_000;
    std::thread::Builder::new()
        .stack_size(1 << 20)
        .spawn(|| {
            let mut e = sort(0);
            for _ in 0..N {
                e = refl(e);
            }
            drop(e);
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A real, working `Nat` -- Zero/Succ and a genuinely computing
/// structural recursor -- exercising `NatPostulates`, the reusable
/// public API extracted from this same construction (see its own
/// module-level doc for the full derivation: which base types get
/// postulated and why, how `Zero`/`Succ` are transported into
/// `ChildTy`, and the "generic recursion/induction principle" gap in
/// `RELATED_WORK.md` §1/§3 this answers). This test is now a
/// *consumer* of that API, not the construction itself -- every
/// `check`/`assert_eq!` below is unchanged from this construction's
/// original, self-contained form, confirming the extraction changed
/// nothing observable.
///
/// `bool_rec` (Bool's own postulated recursor, with its own two
/// computation-rule axioms, also part of `NatPostulates`) is used
/// below to build a genuinely per-case `is_zero : Nat -> Bool`
/// dispatch -- demonstrating the identity recursor's own step (which
/// ignores the tag entirely) isn't the only shape available.
///
/// **A genuine scope boundary that was found here, then fixed at the
/// `Expr::WRec` level** -- deeper than it first looked, and not a
/// function-extensionality gap (an earlier misdiagnosis, corrected in
/// an earlier commit: funext requires both sides to already be
/// well-typed inhabitants of the same Pi-type before it can relate
/// them, and one side here never was one at all). Proving a
/// `bool_rec`-based step's own result concretely (e.g.
/// `is_zero(Zero) = true`) needs more than one `cong1`/`trans_proof`
/// step, since `bool_rec` is postulated and never auto-reduces on its
/// own -- but building that step used to run into a second, deeper
/// problem underneath: `WRec`'s own automatic reduction (`whnf_impl`)
/// built its induction-hypothesis closure with an inert placeholder
/// domain annotation (`sort(0)`) -- harmless for reduction itself
/// (beta substitution never consults a `Lam`'s domain field), but
/// that closure was *unconditionally ill-typed on its own* whenever
/// the step function's `ih` parameter was genuinely used (not just
/// discarded, the way the identity recursor's own step does),
/// blocking it from appearing as a well-typed subterm in any
/// hand-built propositional proof. Fixed now: `Expr::WRec` carries an
/// explicit `children_ty` field (`B`, see its own doc) so
/// `whnf_impl` can give that closure its *honest* domain
/// (`subst_top(children_ty, a)`, i.e. `ChildTy(b)`) instead. The
/// assertions below rebuild that exact closure by hand and confirm it
/// now typechecks at its real domain -- flipped from this test's own
/// original assertion that it was unconditionally rejected, which is
/// why a deliberate revert of the fix (back to the `sort(0)`
/// placeholder) is expected to make this test fail again immediately,
/// not a sign the obstacle has returned.
///
/// `proof.rs`'s own `Ev`/`ev_rec` methodology -- postulate the
/// recursor's existence *and* separately postulate each leaf's own
/// computation rule as an explicit axiom, never relying on any
/// underlying automatic reduction -- remains the necessary shape for
/// `Ev` regardless of this fix, not a historical accident of not
/// having a `Nat` yet: `Ev(params, v)` is an *indexed* family
/// (depends on `params`/`v`, unlike plain `Nat`), so a plain
/// structural recursor over this `Nat` doesn't directly hand you
/// `Ev`'s own induction principle either way, and reusing this `Nat`
/// would still need the exact same per-leaf axiom discipline `Ev`
/// already has -- what it would save is inventing a *new* postulated
/// base type per strategy, not that per-leaf postulation itself. See
/// `RELATED_WORK.md` §3 for the fuller accounting.
#[test]
fn nat_via_w_is_a_genuinely_computing_inductive_type() {
    let mut p = Postulates::new();
    let nat = NatPostulates::new(&mut p);

    let nat_ty = nat.nat_ty(&p);
    p.check(&nat_ty, &sort(0)).expect("Nat := W(Bool, ChildTy) : Type0");

    let zero = nat.zero(&p);
    p.check(&zero, &nat_ty).expect("Zero : Nat");

    // Succ(pred) needs an actual `pred : Nat` in scope -- push one as
    // a fresh postulate, then build Succ against it. Recomputing
    // `nat.nat_ty(&p)`/`nat.zero(&p)` fresh *after* this push (rather
    // than reshifting the snapshots above by hand) is exactly the
    // ergonomic win of `NatPostulates`'s own "always recompute, never
    // cache" design -- the original, self-contained version of this
    // construction needed a manual `shift` here to avoid silently
    // referencing the wrong postulate; this version doesn't.
    let pred_pos = p.push(nat.nat_ty(&p));
    let pred = p.get(pred_pos);
    let nat_ty_here = nat.nat_ty(&p);
    let succ_pred = nat.succ(&p, pred);
    p.check(&succ_pred, &nat_ty_here).expect("Succ(pred) : Nat");

    // Sanity: the identity recursor (mirrors `w_recursor_computes_
    // definitionally`'s own "reconstruct the node unchanged, ignoring
    // ih" step, generalized from that test's constant-children-type W
    // to this Nat's own tag-dependent ChildTy) reduces `Zero`/
    // `Succ(pred)` back to themselves *definitionally* via `wrec`'s
    // own free Sup-reduction alone -- confirming this Nat really is a
    // genuine, computing W-type, not just a well-typed assemblage of
    // postulates.
    let zero_here = nat.zero(&p); // fresh at this (deeper, post-`pred_pos`) depth
    let wa_here = p.get(nat.bool_pos);
    let wb_here = app(shift(&p.get(nat.child_ty_pos), 0, 1), var(0));
    let motive_const = lam(nat_ty_here.clone(), shift(&nat_ty_here, 0, 1)); // \_:Nat. Nat

    let f_ty_d1 = pi(wb_here.clone(), shift(&nat_ty_here, 0, 2));
    let ih_dom_d2 = shift(&wb_here, 0, 1);
    let ih_body_d3 = app(shift(&motive_const, 0, 3), app(var(1), var(0)));
    let ih_ty_d2 = pi(ih_dom_d2, ih_body_d3);
    let step_id = lam(wa_here, lam(f_ty_d1, lam(ih_ty_d2, sup(var(2), var(1)))));

    let id_on_zero = wrec(motive_const.clone(), wb_here.clone(), step_id.clone(), zero_here.clone());
    p.check(&id_on_zero, &nat_ty_here).expect("id-recursor applied to Zero should typecheck at Nat");
    assert_eq!(nf(&id_on_zero), nf(&zero_here), "the identity recursor should reduce Zero back to Zero");

    let id_on_succ = wrec(motive_const, wb_here.clone(), step_id, succ_pred.clone());
    p.check(&id_on_succ, &nat_ty_here).expect("id-recursor applied to Succ(pred) should typecheck at Nat");
    assert_eq!(nf(&id_on_succ), nf(&succ_pred), "the identity recursor should reduce Succ(pred) back to Succ(pred)");

    // A genuinely per-case recursor: is_zero : Nat -> Bool, dispatching
    // on the tag via bool_rec (Bool's own postulated recursor) --
    // demonstrating the identity recursor's own step (which ignores
    // the tag entirely) isn't the only shape available. `bool_rec`
    // doesn't reduce automatically (a postulated recursor, same as
    // any other postulated axiom), so proving `is_zero(Zero) = true`
    // needs one explicit propositional step (`bool_rec_false_eq`)
    // rather than falling straight out of `nf`.
    let wb_here2 = app(shift(&p.get(nat.child_ty_pos), 0, 1), var(0));
    let f_ty_for_c_d1 = arrow(wb_here2.clone(), shift(&nat_ty_here, 0, 1));
    let ih_dom_d2 = shift(&wb_here2, 0, 1);
    let ih_ty_d2 = arrow(ih_dom_d2, shift(&p.get(nat.bool_pos), 0, 2));
    let c_body_d1 = pi(f_ty_for_c_d1, arrow(ih_ty_d2, shift(&p.get(nat.bool_pos), 0, 2)));
    let is_zero_motive_c = lam(p.get(nat.bool_pos), c_body_d1);

    let f_ty_true = arrow(app(p.get(nat.child_ty_pos), p.get(nat.true_pos)), nat_ty_here.clone());
    let ih_ty_true_d1 = arrow(shift(&app(p.get(nat.child_ty_pos), p.get(nat.true_pos)), 0, 1), shift(&p.get(nat.bool_pos), 0, 1));
    let case_true = lam(f_ty_true, lam(ih_ty_true_d1, shift(&p.get(nat.false_pos), 0, 2)));

    let f_ty_false = arrow(app(p.get(nat.child_ty_pos), p.get(nat.false_pos)), nat_ty_here.clone());
    let ih_ty_false_d1 = arrow(shift(&app(p.get(nat.child_ty_pos), p.get(nat.false_pos)), 0, 1), shift(&p.get(nat.bool_pos), 0, 1));
    let case_false = lam(f_ty_false, lam(ih_ty_false_d1, shift(&p.get(nat.true_pos), 0, 2)));

    let is_zero_step = app(app(app(nat.bool_rec(&p), is_zero_motive_c.clone()), case_true.clone()), case_false.clone());
    p.check(&is_zero_step, &pi(p.get(nat.bool_pos), app(shift(&is_zero_motive_c, 0, 1), var(0))))
        .expect("is_zero_step : Pi b:Bool. C(b)");

    let is_zero_motive_const = lam(nat_ty_here.clone(), shift(&p.get(nat.bool_pos), 0, 1)); // \_:Nat. Bool
    let is_zero_on_zero = wrec(is_zero_motive_const.clone(), wb_here2.clone(), is_zero_step.clone(), zero_here.clone());
    p.check(&is_zero_on_zero, &p.get(nat.bool_pos)).expect("is_zero(Zero) : Bool");

    // The obstacle this test used to demonstrate (see git history: an
    // "inert" placeholder domain, `sort(0)`, made `whnf_impl`'s own
    // induction-hypothesis closure unconditionally ill-typed standalone
    // whenever a step genuinely used it) is fixed now: `WRec` carries
    // its own `children_ty` field (`B` from the underlying `W(A,B)`,
    // `infer` cross-checks it against `target`'s own real type -- see
    // `Expr::WRec`'s own doc), and `whnf_impl` uses `subst_top
    // (children_ty, a)` -- `B(a)`, the true children type at tag `a` --
    // as the closure's own domain instead. This rebuilds *exactly* the
    // closure `whnf_impl` now builds internally when reducing
    // `is_zero_on_zero` one step (`is_zero_step` doesn't reduce further
    // on its own -- `bool_rec` is postulated, not a `Lam` -- so this is
    // where `whnf_impl`'s own reduction gets stuck, with this exact
    // closure embedded, unreduced, as `is_zero_step`'s own third
    // argument), confirming it's independently well-typed at its own
    // *honest* domain now, not just "harmless because reduction never
    // consults a `Lam`'s domain field" as before. `zero_child_fn`
    // (`f_zero : ChildTy(false) -> Nat`, `Zero`'s own child function)
    // recomputed fresh at this depth needs only the one extra shift for
    // `rec_step`'s own local binder, not a second one for the depth gap
    // since `pred_pos` was pushed -- the same "recompute, don't reshift
    // a snapshot" benefit as `zero_here` above.
    let f_zero_here = nat.zero_child_fn(&p);
    let honest_domain = subst_top(&wb_here2, &p.get(nat.false_pos));
    let rec_step = lam(
        honest_domain.clone(),
        wrec(shift(&is_zero_motive_const, 0, 1), shift(&wb_here2, 1, 1), shift(&is_zero_step, 0, 1), app(shift(&f_zero_here, 0, 1), var(0))),
    );
    let child_ty_false = app(p.get(nat.child_ty_pos), p.get(nat.false_pos));
    assert!(
        def_eq(&honest_domain, &child_ty_false),
        "subst_top(children_ty, false) should give exactly ChildTy(false), the real children type at the false tag"
    );
    let expected_domain = arrow(child_ty_false, p.get(nat.bool_pos));
    p.check(&rec_step, &expected_domain)
        .expect("with children_ty threaded honestly through whnf_impl's own reduction rule, the induction-hypothesis closure now typechecks at its real domain, not just an inert placeholder");

    // Full end-to-end confirmation: `whnf(is_zero_on_zero)` (which
    // internally builds exactly `rec_step` above) itself still
    // typechecks at `Bool` -- the fix doesn't just make the isolated
    // closure well-typed, it keeps the *whole* one-step reduction
    // well-typed too, stuck-on-a-postulate tail and all.
    let stuck_one_step = whnf(&is_zero_on_zero);
    p.check(&stuck_one_step, &p.get(nat.bool_pos)).expect("whnf(is_zero(Zero)) should still typecheck at Bool after the fix");
    assert_eq!(
        stuck_one_step,
        app(app(app(is_zero_step.clone(), p.get(nat.false_pos)), f_zero_here.clone()), rec_step.clone()),
        "whnf_impl's own stuck reduction should be exactly is_zero_step(false)(f_zero)(rec_step) -- \
         confirming the hand-rebuilt closure above is the *same* one whnf_impl actually produces, \
         not just an independently-typed lookalike"
    );

    // Genuinely finishing `is_zero(Zero) = true` propositionally, now
    // that the closure above is no longer unconditionally ill-typed:
    // `bool_rec_false_eq` (unaffected by the `children_ty` fix, since
    // `bool_rec` is postulated and never reduces on its own) relates
    // `is_zero_step(false)` to `case_false` at `C(false)`; one `cong1`
    // step lifts that (function-application congruence, holding
    // `f_zero_here`/`rec_step` fixed) to a `Bool`-typed equality
    // between the two ways of finishing the call, and `case_false`'s
    // own body ignores both its arguments and returns `true`
    // outright, so its own side reduces the rest of the way for free.
    let bool_ty = p.get(nat.bool_pos);
    let true_val = p.get(nat.true_pos);
    let false_val = p.get(nat.false_pos);
    let is_zero_step_at_false = app(is_zero_step.clone(), false_val.clone());
    let c_false_ty = app(is_zero_motive_c.clone(), false_val.clone());

    let bfe_inst = app(app(app(nat.bool_rec_false_eq(&p), is_zero_motive_c.clone()), case_true.clone()), case_false.clone());
    p.check(
        &bfe_inst,
        &id(c_false_ty.clone(), is_zero_step_at_false.clone(), case_false.clone()),
    )
    .expect("bool_rec_false_eq instantiated at (is_zero_motive_c, case_true, case_false) should typecheck");

    // f_cong : C(false) -> Bool := \h. h(f_zero_here)(rec_step)
    let f_cong = lam(c_false_ty.clone(), app(app(var(0), shift(&f_zero_here, 0, 1)), shift(&rec_step, 0, 1)));
    let cong_step = cong1(&c_false_ty, &bool_ty, &f_cong, is_zero_step_at_false, case_false.clone(), bfe_inst);

    // `refl` bridges `is_zero_on_zero` to its own one-step reduction
    // (definitionally equal, `whnf` being one particular strategy for
    // reaching a shared normal form) -- `trans_proof` then chains that
    // with `cong_step` (whose own type, `Id(Bool, f_cong(is_zero_step
    // (false)), f_cong(case_false))`, is itself definitionally equal
    // to `Id(Bool, stuck_one_step, true)` once both sides beta-reduce,
    // `case_false`'s own body reducing all the way to `true`) to land
    // on the final result.
    let bridge = refl(is_zero_on_zero.clone());
    let final_proof = trans_proof(&bool_ty, &is_zero_on_zero, &stuck_one_step, &true_val, bridge, cong_step);
    p.check(&final_proof, &id(bool_ty, is_zero_on_zero, true_val))
        .expect("is_zero(Zero) = true should now be provable propositionally");
}

#[test]
fn a_tagged_selector_built_via_wrec_typechecks_a_pair_for_a_symbolic_tag() {
    // Prototype for RELATED_WORK.md sec 14's open question: can a
    // Sigma-tagged "either T1 or T2" encoding typecheck a Pair for a
    // SYMBOLIC (universally quantified) tag, not just a concrete one?
    // Hypothesis: build both the type selector (`fam`) and the paired
    // value as WRec applications sharing the same underlying "motive"
    // Lam -- WRec's own typing rule hands back `app(motive, target)`
    // as the type *by construction* (kernel.rs's own `infer`, `Expr::
    // WRec` case), so `def_eq` between the value's inferred type and
    // `fam`'s substituted form reduces to ordinary, unconditional
    // beta -- never needing the tag itself to reduce to a concrete Sup.
    let mut p = Postulates::new();
    let nat = NatPostulates::new(&mut p);

    // Push the tag as an abstract postulate up front -- genuinely
    // symbolic, not a concrete Sup value -- so everything built below
    // is naturally index-consistent with it already in scope.
    let a_pos = p.push(nat.nat_ty(&p));

    // sort_rec : Pi C:(Bool -> Sort1). C(true) -> C(false) -> Pi b:Bool. C(b)
    // -- bool_rec's own shape (`wrap_c_ct_cf`), but targeting Sort(1)
    // so C can select between *types*, not just Sort0 values (Nat
    // Postulates' own bool_rec hardcodes Sort(0) -- see this file's own
    // is_zero test and RELATED_WORK.md's universe-mismatch finding).
    fn wrap_c_ct_cf_sort1(bool_ref: &Expr, true_ref: &Expr, false_ref: &Expr, body_d3: Expr) -> Expr {
        let c_ty = arrow(bool_ref.clone(), sort(1));
        let true_d1 = shift(true_ref, 0, 1);
        let false_d2 = shift(false_ref, 0, 2);
        let pi_cf = pi(app(var(1), false_d2), body_d3);
        let pi_ct = pi(app(var(0), true_d1), pi_cf);
        pi(c_ty, pi_ct)
    }
    // Mirrors `infer`'s own `Expr::WRec` case exactly: returns
    // (per-tag body, one binder deep; full `Pi a:wa. ...`).
    fn wrec_step_type(wa: &Expr, wb: &Expr, w_ty0: &Expr, motive: &Expr) -> (Expr, Expr) {
        let f_dom_d1 = wb.clone();
        let f_ty_d1 = pi(f_dom_d1, shift(w_ty0, 0, 2));
        let ih_dom_d2 = shift(wb, 0, 1);
        let motive_d3 = shift(motive, 0, 3);
        let ih_body_d3 = app(motive_d3, app(var(1), var(0)));
        let ih_ty_d2 = pi(ih_dom_d2, ih_body_d3);
        let motive_d2 = shift(motive, 0, 2);
        let concl_ty_d2 = app(motive_d2, sup(var(1), var(0)));
        let arrow_ty_d2 = pi(ih_ty_d2, shift(&concl_ty_d2, 0, 1));
        let per_tag_body_d1 = pi(f_ty_d1, arrow_ty_d2);
        let full = pi(wa.clone(), per_tag_body_d1.clone());
        (per_tag_body_d1, full)
    }

    let sort_rec_body_d3 = pi(shift(&p.get(nat.bool_pos), 0, 3), app(var(3), var(0)));
    let sort_rec_ty = wrap_c_ct_cf_sort1(&p.get(nat.bool_pos), &p.get(nat.true_pos), &p.get(nat.false_pos), sort_rec_body_d3);
    let sort_rec_pos = p.push(sort_rec_ty);

    // sort_rec_true_eq : Pi C ct cf. Id(C(true), sort_rec(C,ct,cf)(true), ct)
    let true_d3 = shift(&p.get(nat.true_pos), 0, 3);
    let applied_d3 = app(app(app(shift(&p.get(sort_rec_pos), 0, 3), var(2)), var(1)), var(0));
    let true_eq_body_d3 = id(app(var(2), true_d3.clone()), app(applied_d3, true_d3), var(1));
    let sort_rec_true_eq_ty = wrap_c_ct_cf_sort1(&p.get(nat.bool_pos), &p.get(nat.true_pos), &p.get(nat.false_pos), true_eq_body_d3);
    let sort_rec_true_eq_pos = p.push(sort_rec_true_eq_ty);

    // sort_rec_false_eq : Pi C ct cf. Id(C(false), sort_rec(C,ct,cf)(false), cf)
    let false_d3 = shift(&p.get(nat.false_pos), 0, 3);
    let applied_d3b = app(app(app(shift(&p.get(sort_rec_pos), 0, 3), var(2)), var(1)), var(0));
    let false_eq_body_d3 = id(app(var(2), false_d3.clone()), app(applied_d3b, false_d3), var(0));
    let sort_rec_false_eq_ty = wrap_c_ct_cf_sort1(&p.get(nat.bool_pos), &p.get(nat.true_pos), &p.get(nat.false_pos), false_eq_body_d3);
    let sort_rec_false_eq_pos = p.push(sort_rec_false_eq_ty);

    // --- Fresh from here on: everything (a, sort_rec, its two
    // computation-rule axioms) is already in scope.
    let nat_ty = nat.nat_ty(&p);
    let bool_ty = nat.bool_ty(&p);
    let true_val = nat.true_(&p);
    let false_val = nat.false_(&p);
    let sort_rec = p.get(sort_rec_pos);
    let wb = app(shift(&p.get(nat.child_ty_pos), 0, 1), var(0)); // ChildTy(b), one binder (b)

    // type_motive : Nat -> Sort0, constant -- `fam`'s own overall type
    // doesn't need to vary per branch; what varies per branch is
    // `step`'s own *value*, selected via sort_rec below.
    let type_motive = lam(nat_ty.clone(), sort(0));
    p.check(&type_motive, &arrow(nat_ty.clone(), sort(1))).expect("type_motive : Nat -> Sort1");

    let (type_per_tag_d1, type_expected_step_ty) = wrec_step_type(&bool_ty, &wb, &nat_ty, &type_motive);
    let type_motive_c = lam(bool_ty.clone(), type_per_tag_d1.clone());

    // Two genuinely distinct Sort0 types to select between -- stand-ins
    // for Clo_1/Clo_2.
    let clo1_ty = nat.unit_ty(&p);
    let clo2_ty = nat_ty.clone();

    let case_true_ty_expected = subst_top(&type_per_tag_d1, &true_val);
    let Expr::Pi(f_dom_true, rest_true) = &case_true_ty_expected else { panic!("expected Pi") };
    let Expr::Pi(ih_dom_true, _) = &**rest_true else { panic!("expected Pi") };
    let case_true_ty = lam((**f_dom_true).clone(), lam((**ih_dom_true).clone(), shift(&clo1_ty, 0, 2)));
    p.check(&case_true_ty, &case_true_ty_expected).expect("case_true_ty : type_motive_c(true)");

    let case_false_ty_expected = subst_top(&type_per_tag_d1, &false_val);
    let Expr::Pi(f_dom_false, rest_false) = &case_false_ty_expected else { panic!("expected Pi") };
    let Expr::Pi(ih_dom_false, _) = &**rest_false else { panic!("expected Pi") };
    let case_false_ty = lam((**f_dom_false).clone(), lam((**ih_dom_false).clone(), shift(&clo2_ty, 0, 2)));
    p.check(&case_false_ty, &case_false_ty_expected).expect("case_false_ty : type_motive_c(false)");

    let type_step = app(app(app(sort_rec.clone(), type_motive_c.clone()), case_true_ty.clone()), case_false_ty.clone());
    p.check(&type_step, &type_expected_step_ty).expect("type_step : Pi b:Bool. type_motive_c(b)");

    // fam := wrec(type_motive, ChildTy(Var0), type_step, Var(0)) --
    // Sigma's own open family body, one binder under the tag.
    let fam = wrec(shift(&type_motive, 0, 1), shift(&wb, 1, 1), shift(&type_step, 0, 1), var(0));

    let sigma_ty = sigma(nat_ty.clone(), fam.clone());
    p.check(&sigma_ty, &sort(0)).expect("Sigma(Nat, fam) : Sort0");

    // --- THE KEY CLAIM: Pair(fam, a, b) typechecks for a's tag being a
    // genuinely SYMBOLIC (universally quantified) postulate, not a
    // concrete Sup value -- unlike the earlier tagged-Sigma
    // investigation (RELATED_WORK.md sec 14), which needed `a` concrete.
    let a = p.get(a_pos);

    // value_motive := \x:Nat. fam -- literally reuses `fam` as the
    // Lam's own body, so `value_motive(a)` beta-reduces (unconditionally,
    // for ANY a, symbolic or not) to exactly `subst_top(fam, a)`.
    let value_motive = lam(nat_ty.clone(), fam.clone());
    p.check(&value_motive, &arrow(nat_ty.clone(), sort(0))).expect("value_motive : Nat -> Sort0");

    let (value_per_tag_d1, value_expected_step_ty) = wrec_step_type(&bool_ty, &wb, &nat_ty, &value_motive);
    let value_motive_c = lam(bool_ty.clone(), value_per_tag_d1.clone());

    let value_case_true_expected = subst_top(&value_per_tag_d1, &true_val);
    let Expr::Pi(vf_dom_true, vrest_true) = &value_case_true_expected else { panic!("expected Pi") };
    let Expr::Pi(vih_dom_true, _) = &**vrest_true else { panic!("expected Pi") };

    let value_case_false_expected = subst_top(&value_per_tag_d1, &false_val);
    let Expr::Pi(vf_dom_false, vrest_false) = &value_case_false_expected else { panic!("expected Pi") };
    let Expr::Pi(vih_dom_false, _) = &**vrest_false else { panic!("expected Pi") };

    // Rebuild, under `case_*_val`'s own f/ih binders (depth 2), the
    // exact induction-hypothesis closure `whnf_impl`'s own WRec-Sup
    // rule auto-builds when reducing `value_motive(sup(tag,f))` --
    // mirroring `nat_via_w_is_a_genuinely_computing_inductive_type`'s
    // own hand-rebuild of `rec_step`, generalized to a bound `f`
    // instead of a closed one.
    fn rebuild_rec_step_d2(type_motive: &Expr, wb: &Expr, type_step: &Expr, tag: &Expr, f_ref: &Expr) -> Expr {
        let tm2 = shift(type_motive, 0, 2);
        let wb2 = shift(wb, 1, 2);
        let ts2 = shift(type_step, 0, 2);
        let tag2 = shift(tag, 0, 2);
        lam(
            subst_top(&wb2, &tag2),
            wrec(shift(&tm2, 0, 1), shift(&wb2, 1, 1), shift(&ts2, 0, 1), app(shift(f_ref, 0, 1), var(0))),
        )
    }

    // Bridges `type_step(tag)(f)(rec_step) = case_ty(f)(rec_step)`
    // propositionally via `sort_rec_{true,false}_eq` + one `cong1`
    // (the `f_cong` trick `is_zero`'s own proof above already uses),
    // then `transport`s a real, concrete witness across it.
    #[allow(clippy::too_many_arguments)]
    fn build_case_val(
        p: &Postulates,
        type_motive_c: &Expr,
        type_step: &Expr,
        case_ty: &Expr,
        eq_ref: &Expr,
        case_true_ty: &Expr,
        case_false_ty: &Expr,
        tag: &Expr,
        f_dom: &Expr,
        ih_dom: &Expr,
        rec_step: &Expr,
        witness_ty: &Expr,
        witness: &Expr,
    ) -> Expr {
        let f_ref = var(1);
        let tag2 = shift(tag, 0, 2);
        let type_step_at_tag = app(shift(type_step, 0, 2), tag2.clone());
        let target_ty = app(app(type_step_at_tag.clone(), f_ref.clone()), rec_step.clone());

        let c_at_tag = app(shift(type_motive_c, 0, 2), tag2.clone());
        let eq_inst = app(app(app(shift(eq_ref, 0, 2), shift(type_motive_c, 0, 2)), shift(case_true_ty, 0, 2)), shift(case_false_ty, 0, 2));
        let f_cong = lam(c_at_tag.clone(), app(app(var(0), shift(&f_ref, 0, 1)), shift(rec_step, 0, 1)));
        let cong_step = cong1(&c_at_tag, &sort(0), &f_cong, type_step_at_tag, shift(case_ty, 0, 2), eq_inst);

        // `witness`/`witness_ty` are given at *ambient* (outer-test)
        // depth -- everything else here is already shifted for this
        // function's own depth-2 (f, ih) scope, so these need the same
        // +2 shift for `sym`/`transport` to compare like-for-like.
        let witness_ty2 = shift(witness_ty, 0, 2);
        let witness2 = shift(witness, 0, 2);
        let bridge = sym(&sort(0), &target_ty, &witness_ty2, cong_step);
        let _ = p;
        lam(f_dom.clone(), lam(ih_dom.clone(), transport(0, witness_ty2, target_ty, bridge, witness2)))
    }

    let f_ref_true = var(1);
    let rec_step_true = rebuild_rec_step_d2(&type_motive, &wb, &type_step, &true_val, &f_ref_true);
    let star = nat.star(&p);
    let case_true_val = build_case_val(
        &p,
        &type_motive_c,
        &type_step,
        &case_true_ty,
        &p.get(sort_rec_true_eq_pos),
        &case_true_ty,
        &case_false_ty,
        &true_val,
        vf_dom_true,
        vih_dom_true,
        &rec_step_true,
        &clo1_ty,
        &star,
    );
    p.check(&case_true_val, &value_case_true_expected).expect("case_true_val : value_motive_c(true)");

    let f_ref_false = var(1);
    let rec_step_false = rebuild_rec_step_d2(&type_motive, &wb, &type_step, &false_val, &f_ref_false);
    let zero_witness = nat.zero(&p);
    let case_false_val = build_case_val(
        &p,
        &type_motive_c,
        &type_step,
        &case_false_ty,
        &p.get(sort_rec_false_eq_pos),
        &case_true_ty,
        &case_false_ty,
        &false_val,
        vf_dom_false,
        vih_dom_false,
        &rec_step_false,
        &clo2_ty,
        &zero_witness,
    );
    p.check(&case_false_val, &value_case_false_expected).expect("case_false_val : value_motive_c(false)");

    // `value_motive_c`'s own final codomain is `value_motive(sup(b,f))`
    // -- an *application*, itself Sort0-typed (unlike `type_motive_c`'s
    // literal `sort(0)` codomain, which is Sort1-typed as a value) --
    // so `value_motive_c : Bool -> Sort0` exactly matches the ordinary,
    // already-built `nat.bool_rec` (no new postulate needed here).
    let value_step = app(app(app(nat.bool_rec(&p), value_motive_c.clone()), case_true_val), case_false_val);
    p.check(&value_step, &value_expected_step_ty).expect("value_step : Pi b:Bool. value_motive_c(b)");

    // b_val := wrec(value_motive, ChildTy(Var0), value_step, a) --
    // standalone, at the SAME (ambient) depth as `a` itself, no extra
    // binder (unlike `fam`, this isn't going *inside* anything).
    let b_val = wrec(value_motive.clone(), wb.clone(), value_step, a.clone());
    let expected_b_ty = subst_top(&fam, &a);
    p.check(&b_val, &expected_b_ty).expect("b_val : subst_top(fam, a) -- the core claim, isolated");

    // Sanity: `a` is genuinely symbolic, not secretly concrete -- whnf
    // doesn't reduce a bare postulate reference to `Sup(..)`, and
    // `fam(a)` doesn't secretly normalize to some closed Sort0 type
    // either (both would make this whole exercise vacuous).
    assert_eq!(whnf(&a), a, "the tag must stay an unreduced postulate reference, not secretly a concrete Sup");
    assert!(
        !matches!(nf(&expected_b_ty), Expr::Sort(_) | Expr::W(..)),
        "fam(a) must stay stuck for symbolic a, not secretly collapse to a closed type: {:?}",
        nf(&expected_b_ty)
    );

    // --- THE ULTIMATE CLAIM: Pair(fam, a, b_val) typechecks as
    // Sigma(Nat, fam), for `a` a genuinely symbolic tag -- unlike the
    // earlier tagged-Sigma investigation (RELATED_WORK.md sec 14),
    // which needed `a` concrete before `Pair`'s own definitional-
    // equality check could ever succeed.
    let pr = pair(fam.clone(), a.clone(), b_val);
    let pr_ty = p.infer(&pr).expect("Pair(fam, a, b_val) should typecheck for a SYMBOLIC tag");
    assert!(def_eq(&pr_ty, &sigma_ty), "Pair's own inferred type should be Sigma(Nat, fam): got {pr_ty:?}");
}

#[test]
fn shift_by_zero_is_the_identity_including_through_binders() {
    // Exercises every variant, including ones whose subterms sit under
    // an extra binder (Pi/Lam/W bump `cutoff` for their second field) --
    // shift's `amount == 0` fast path returns `e.clone()` without
    // recursing at all, so this confirms that's equivalent to the full
    // structural recursion for a term where it'd actually matter if the
    // fast path skipped something it shouldn't.
    let e = pi(
        sort(0),
        jelim(
            lam(var(0), wty(var(1), sup(var(0), var(2)))),
            refl(var(0)),
            var(1),
            var(2),
            wrec(var(0), var(1), var(2), var(3)),
        ),
    );
    assert_eq!(shift(&e, 0, 0), e);
    assert_eq!(shift(&e, 3, 0), e);
}

#[test]
fn universes_stratify() {
    assert_eq!(typecheck(&sort(0)).unwrap(), sort(1));
    assert_eq!(typecheck(&sort(5)).unwrap(), sort(6));
}

#[test]
fn a_maximal_universe_level_is_a_clean_type_error_not_an_overflow_panic() {
    // Type_{u32::MAX} has no successor sort representable in this
    // encoding -- infer's own `i.checked_add(1)` reports that as an
    // ordinary Err, rather than panicking on the arithmetic overflow
    // `i + 1` would otherwise trigger (checked in debug builds, wrapping
    // silently to Type0 in release -- neither of which is the honest
    // "this term doesn't typecheck" answer every other rejection here
    // gives).
    assert!(typecheck(&sort(u32::MAX)).is_err());
}

#[test]
fn identity_function_typechecks() {
    // \A:Type0. \x:A. x  :  Pi A:Type0. A -> A
    let f = lam(sort(0), lam(var(0), var(0)));
    let ty = typecheck(&f).unwrap();
    let expected = pi(sort(0), arrow(var(0), var(0)));
    assert!(def_eq(&ty, &expected), "got {ty:?}");
}

#[test]
fn refl_typechecks_for_a_postulated_element() {
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0)); // A : Type0
    let a0_pos = p.push(p.get(a_pos)); // a0 : A

    let a0 = p.get(a0_pos);
    let ty = p.infer(&refl(a0.clone())).unwrap();
    assert!(def_eq(&ty, &id(p.get(a_pos), a0.clone(), a0)));
}

/// `A : Type0` and `a : A` as globals: the environment the tests below
/// type constants in.
fn two_globals() -> Globals {
    let mut g = Globals::new();
    g.push_back(sort(0));
    g.push_back(Expr::Const(0));
    g
}

#[test]
fn a_const_has_its_globals_type() {
    let g = two_globals();
    let a = Expr::Const(1);
    assert_eq!(infer_in(&g, &Ctx::new(), &a), Ok(Expr::Const(0)));
    assert_eq!(check_in(&g, &Ctx::new(), &refl(a.clone()), &id(Expr::Const(0), a.clone(), a)), Ok(()));
    // No shift: the same `Const` has the same type under a binder.
    assert_eq!(infer_in(&g, &Ctx::new(), &lam(sort(0), Expr::Const(1))), Ok(pi(sort(0), Expr::Const(0))));
}

#[test]
fn a_const_past_the_environment_is_rejected() {
    assert!(infer_in(&two_globals(), &Ctx::new(), &Expr::Const(2)).is_err());
    assert!(infer(&Ctx::new(), &Expr::Const(0)).is_err(), "no globals at all");
}

/// `Const(l)` names a global, never a binder the kernel pushed. With one
/// global, `Const(1)` under a binder would be that binder if constants
/// and binders shared one vector, and `(λx:A. Const(1)) a` would then
/// reduce to a `Const(1)` that refers to nothing.
#[test]
fn a_const_at_a_binders_position_is_rejected() {
    let mut g = Globals::new();
    g.push_back(sort(0));
    assert!(infer_in(&g, &Ctx::new(), &lam(Expr::Const(0), Expr::Const(1))).is_err());
    let mut ctx = Ctx::new();
    ctx.push_back(Expr::Const(0));
    assert!(infer_in(&g, &ctx, &Expr::Const(1)).is_err(), "a caller's local isn't a global either");
}

/// A global's type must be closed: no loose `Var` (it would mean a
/// different thing at every depth) and no `Free`.
#[test]
fn a_global_whose_type_is_open_is_rejected() {
    for bad in [var(0), Expr::Free(0), pi(sort(0), var(1))] {
        let mut g = Globals::new();
        g.push_back(bad.clone());
        assert!(infer_in(&g, &Ctx::new(), &Expr::Const(0)).is_err(), "{bad:?}");
    }
}

/// A `Free` fails the check wherever it sits, including where `infer`
/// never looks: a lambda's domain under `check` (compared by `def_eq`
/// only) and the expected type, each under a redex that reduces the
/// `Free` away. `infer_in` faces the same trap: `infer` hands an
/// `App`'s argument to `check_rc`, so a `Free` hidden in that
/// argument's own lambda domain (or, for `WRec`, in `children_ty`)
/// reduces away under `def_eq` and is never itself inferred -- this is
/// the case the final review's counterexample found with the door
/// removed (`RELATED_WORK.md` §67).
#[test]
fn a_free_is_rejected_everywhere() {
    let g = two_globals();
    let none = Ctx::new();
    let hide = |x: Expr| app(lam(Expr::Free(0), x), Expr::Const(1)); // reduces to x
    let unhide = |x: Expr| app(lam(Expr::Const(0), x), Expr::Const(1));
    assert!(infer_in(&g, &none, &Expr::Free(0)).is_err());
    assert!(infer_in(&g, &none, &lam(sort(0), Expr::Free(0))).is_err(), "under a binder");
    assert!(infer_in(&g, &none, &pi(Expr::Free(0), sort(0))).is_err(), "in a type");
    assert!(check_in(&g, &none, &Expr::Const(1), &hide(Expr::Const(0))).is_err(), "in the expected type");
    let lam_hidden_dom = lam(hide(Expr::Const(0)), Expr::Const(1));
    assert!(check_in(&g, &none, &lam_hidden_dom, &pi(Expr::Const(0), Expr::Const(0))).is_err(), "in a checked lambda's domain");
    let mut ctx = Ctx::new();
    ctx.push_back(Expr::Free(0));
    assert!(infer_in(&g, &ctx, &var(0)).is_err(), "in a context entry");

    // `infer_in`, not just `check_in`: an `App`'s argument goes to
    // `check_rc`, whose `Lam` rule against a `Pi` compares the domain
    // by `def_eq` and never infers it. With the door removed, this
    // exact term type-checked and returned `Ok(Const(0))` -- the
    // hidden `Free` in the argument's lambda domain reduced away
    // under `def_eq` without ever being inferred.
    let arg_hidden_dom = app(
        lam(arrow(Expr::Const(0), Expr::Const(0)), Expr::Const(1)),
        lam(hide(Expr::Const(0)), Expr::Const(1)),
    );
    assert!(infer_in(&g, &none, &arg_hidden_dom).is_err(), "in an argument's lambda domain");
    let arg_unhidden_dom = app(
        lam(arrow(Expr::Const(0), Expr::Const(0)), Expr::Const(1)),
        lam(unhide(Expr::Const(0)), Expr::Const(1)),
    );
    assert_eq!(infer_in(&g, &none, &arg_unhidden_dom), Ok(Expr::Const(0)));

    // Same trap in `WRec`: `children_ty` is only compared by `def_eq`
    // against the target's own inferred children type, never inferred
    // itself. Build a well-typed `W(A,Bc)` recursor entirely from
    // globals, so `children_ty` can hide a `Free` behind a redex.
    let a_ty = Expr::Const(0); // A : Type0 (g[0])
    let bc_ty = Expr::Const(1); // Bc : Type0 (g[1])
    let mut gw = Globals::new();
    gw.push_back(sort(0)); // 0: A : Type0
    gw.push_back(sort(0)); // 1: Bc : Type0
    gw.push_back(a_ty.clone()); // 2: a0 : A
    gw.push_back(arrow(bc_ty.clone(), wty(a_ty.clone(), bc_ty.clone()))); // 3: f0 : Bc -> W(A,Bc)
    let a0 = Expr::Const(2);
    let f0 = Expr::Const(3);
    let w_ty = wty(a_ty.clone(), bc_ty.clone());
    let motive = lam(w_ty.clone(), w_ty.clone()); // constant motive
    let f_ty = pi(bc_ty.clone(), w_ty.clone());
    let ih_ty = pi(bc_ty.clone(), app(motive.clone(), app(var(1), var(0))));
    let step = lam(a_ty.clone(), lam(f_ty, lam(ih_ty, sup(var(2), var(1)))));
    let target = sup(a0, f0);
    let wrec_good = wrec(motive.clone(), bc_ty.clone(), step.clone(), target.clone());
    assert_eq!(infer_in(&gw, &none, &wrec_good), Ok(app(motive.clone(), target.clone())), "unhidden children_ty");
    let wrec_hidden_children_ty = wrec(motive, hide(bc_ty), step, target);
    assert!(infer_in(&gw, &none, &wrec_hidden_children_ty).is_err(), "a Free hidden under a redex in children_ty");

    // The same terms without the `Free` are fine, so the rejections
    // above are the `Free`'s doing.
    assert_eq!(check_in(&g, &none, &Expr::Const(1), &unhide(Expr::Const(0))), Ok(()));
    assert_eq!(check_in(&g, &none, &lam(unhide(Expr::Const(0)), Expr::Const(1)), &pi(Expr::Const(0), Expr::Const(0))), Ok(()));
}

/// `check_in` checks its claim is a type before checking the proof, as
/// Lean's `check_constant_val` and Coq's `infer_definition` do
/// (RELATED_WORK §67). Without that, a malformed claim is "proved".
#[test]
fn a_claim_that_isnt_a_type_is_rejected() {
    let g = two_globals();
    let none = Ctx::new();
    let a = Expr::Const(1); // a term of type A, not a type
    assert!(check_in(&g, &none, &lam(a.clone(), var(0)), &pi(a.clone(), a.clone())).is_err(), "Π(x:a). a");
    let ghost = app(lam(Expr::Const(99), Expr::Const(0)), a.clone()); // reduces to A
    assert!(check_in(&g, &none, &a, &ghost).is_err(), "a claim naming a constant that doesn't exist");
    // Well-formed claims still check.
    assert_eq!(check_in(&g, &none, &lam(Expr::Const(0), var(0)), &pi(Expr::Const(0), Expr::Const(0))), Ok(()));
    assert_eq!(check_in(&g, &none, &a, &app(lam(Expr::Const(0), Expr::Const(0)), a.clone())), Ok(()));
}

/// Checking a lambda against a Π infers its annotation to a `Sort`,
/// as `infer` does, rather than only comparing it with the domain:
/// here the claim is well-formed and the annotation reduces to the
/// domain, but names a constant that doesn't exist.
#[test]
fn a_checked_lambdas_annotation_must_be_a_type() {
    let g = two_globals();
    let none = Ctx::new();
    let ghost = app(lam(Expr::Const(99), Expr::Const(0)), Expr::Const(1)); // reduces to A
    let claim = pi(Expr::Const(0), Expr::Const(0));
    assert!(check_in(&g, &none, &lam(ghost, var(0)), &claim).is_err());
    let fine = app(lam(Expr::Const(0), Expr::Const(0)), Expr::Const(1));
    assert_eq!(check_in(&g, &none, &lam(fine, var(0)), &claim), Ok(()));
}

#[test]
fn w_recursor_computes_definitionally() {
    // Postulate a base type A with a witness a0, a (tag-independent)
    // children-index type Bc, and a children function
    // f0 : Bc -> W(A, Bc). See `Postulates` docs above for why this is
    // postulated rather than derived.
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0)); // A : Type0
    let a0_pos = p.push(p.get(a_pos)); // a0 : A
    let bc_pos = p.push(sort(0)); // Bc : Type0
    let w_ty_pre = wty(p.get(a_pos), shift(&p.get(bc_pos), 0, 1));
    let f0_pos = p.push(arrow(p.get(bc_pos), w_ty_pre)); // f0 : Bc -> W(A,Bc)

    // p.globals now has 4 entries; re-fetch references at this depth.
    let a_ref = p.get(a_pos);
    let bc_ref = p.get(bc_pos);
    let w_ty = wty(a_ref.clone(), shift(&bc_ref, 0, 1));
    let target = sup(p.get(a0_pos), p.get(f0_pos));
    assert!(def_eq(&p.infer(&target).unwrap(), &w_ty));

    // motive := \_ : W(A,Bc). W(A,Bc)   (constant motive)
    let motive = lam(w_ty.clone(), shift(&w_ty, 0, 1));

    // step := \a:A. \f:(Bc->W). \ih:(Pi y:Bc. motive (f y)). sup(a, f)
    // i.e. "reconstruct the node, ignoring the induction hypothesis" —
    // this makes `wrec(motive, step, _)` the identity on W, defined via
    // its own recursor rather than as a primitive.
    // Note: `pi`, not `arrow` -- `shift(&w_ty, 0, 2)` already lands the
    // codomain at the right depth (one deeper than this Pi's own
    // placement at depth1); wrapping it in `arrow` would shift it twice.
    let f_ty_d1 = pi(shift(&bc_ref, 0, 1), shift(&w_ty, 0, 2));
    let ih_ty_d2 = pi(
        shift(&bc_ref, 0, 2),
        app(shift(&motive, 0, 3), app(var(1), var(0))), // motive (f y)
    );
    let step = lam(a_ref, lam(f_ty_d1, lam(ih_ty_d2, sup(var(2), var(1)))));

    let reduced = wrec(motive, shift(&bc_ref, 0, 1), step, target.clone());
    p.check(&reduced, &w_ty).expect("wrec application should typecheck");
    // The payoff of choosing W over an impredicative/Church encoding:
    // this holds by `refl` alone — the recursor genuinely *computes*,
    // it doesn't just make the equation provable with extra work.
    p.check(&refl(target.clone()), &id(w_ty, reduced, target))
        .expect("wrec(motive, step, sup(a,f)) should reduce definitionally to sup(a,f)");
}

#[test]
fn sup_rejects_a_children_function_whose_codomain_genuinely_depends_on_its_own_argument() {
    // `Sup(a, f)`'s own typing rule (see its doc) requires `f`'s
    // codomain to be a constant `W(A,B)`, independent of `f`'s own
    // bound argument -- otherwise `subst_top(cod, a)` is only ever
    // validated at this one concrete `a`, silently trusting every
    // other point of `f`'s domain agrees. Build a minimal witness
    // where that's structurally false: `g : D -> Type0` postulated
    // opaque (so its result genuinely varies per input, as far as the
    // kernel can tell -- no reduction could ever prove otherwise),
    // and `mk : Pi x:D. g(x)`, so `mk` itself has exactly the
    // offending shape `Pi x:D. cod` with `cod = g(x)` mentioning `x`.
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0)); // A : Type0
    let a0_pos = p.push(p.get(a_pos)); // a0 : A
    let d_pos = p.push(sort(0)); // D : Type0
    let g_pos = p.push(arrow(p.get(d_pos), sort(0))); // g : D -> Type0
    let mk_ty = pi(p.get(d_pos), app(shift(&p.get(g_pos), 0, 1), var(0))); // Pi x:D. g(x)
    let mk_pos = p.push(mk_ty);

    let target = sup(p.get(a0_pos), p.get(mk_pos));
    let err = p.infer(&target).expect_err("a dependent codomain must be rejected, not silently trusted");
    assert!(
        err.contains("must not depend"),
        "expected the dependent-codomain error, got: {err}"
    );
}

#[test]
fn is_var_free_tracks_binder_depth_and_is_checked_against_normal_form_not_raw_syntax() {
    // `Sup`'s new occurs-check (above) runs `is_var_free` on `cod`'s
    // *normal form*, not its raw syntax, precisely so a codomain that
    // only syntactically mentions its own argument -- but beta-
    // reduces free of it -- is still accepted rather than wrongly
    // rejected. Exercise `is_var_free` itself directly, including
    // that specific reduces-away shape, rather than through the
    // fragile nested-W-type indexing a full `Sup` witness would need.
    assert!(is_var_free(&var(0), 0));
    assert!(!is_var_free(&var(1), 0));
    // `\_:Sort0. (outer Var(0))`, written under one more binder as
    // `Var(1)` -- does this Lam depend on the *outer* Var(0)? Yes.
    assert!(is_var_free(&lam(sort(0), var(1)), 0));
    // `\_:Sort0. Var(0)` (the lambda's *own* argument) -- does this
    // depend on something *outside* the lambda at outer-index 0? No.
    assert!(!is_var_free(&lam(sort(0), var(0)), 0));

    // `(\_:Sort0. Sort(1)) (Var 0)` mentions `Var(0)` syntactically as
    // the application's argument, but beta-reduces to plain
    // `Sort(1)`, genuinely independent of it.
    let redex = app(lam(sort(0), sort(1)), var(0));
    assert!(is_var_free(&redex, 0), "the raw syntax does mention Var(0)");
    assert!(!is_var_free(&nf(&redex), 0), "but it reduces away");
}

#[test]
fn sigma_pairing_typechecks_and_projects_by_refl() {
    // A postulated type A, an element a0:A, a second type B, an
    // element b0:B -- a non-dependent pair Sigma(A, \_.B), the
    // simplest instance, isolating pairing/projection from
    // dependency itself (see
    // `sigma_family_genuinely_varies_with_the_tag` below for a case
    // that needs real dependency).
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0));
    let a0_pos = p.push(p.get(a_pos));
    let b_pos = p.push(sort(0));
    let b0_pos = p.push(p.get(b_pos));

    let a_ref = p.get(a_pos);
    let a0_ref = p.get(a0_pos);
    let b_ref = p.get(b_pos);
    let b0_ref = p.get(b0_pos);

    let fam = shift(&b_ref, 0, 1); // \_:A. B, written one binder deeper
    let sig_ty = sigma(a_ref.clone(), fam.clone());
    let target = pair(fam.clone(), a0_ref.clone(), b0_ref.clone());
    p.check(&target, &sig_ty).expect("pair(fam, a0, b0) : Sigma(A, fam)");

    // motive := \_:Sigma(A,fam). A  (constant motive)
    let motive = lam(sig_ty.clone(), shift(&a_ref, 0, 1));
    // step := \a:A. \b:B. a  -- i.e. "fst"
    let step = lam(a_ref.clone(), lam(fam, var(1)));
    let reduced = sigrec(motive, step, target.clone());
    p.check(&reduced, &a_ref).expect("sigrec application should typecheck");
    // The same payoff `w_recursor_computes_definitionally` already
    // established for `W`: this holds by `refl` alone -- the
    // recursor genuinely *computes*, not just propositionally.
    p.check(&refl(a0_ref.clone()), &id(a_ref, reduced, a0_ref))
        .expect("sigrec(motive, step, pair(fam,a0,b0)) should reduce definitionally to a0");
}

#[test]
fn sigma_family_genuinely_varies_with_the_tag() {
    // A postulated type A and element a0:A; fam(x) := Id(A, x, a0),
    // a family that genuinely varies with the tag (not just carried
    // along unused, unlike the constant-family test above) --
    // Sigma(A,fam) is "an x together with a proof that x=a0".
    // pair(fam, a0, refl(a0)) should typecheck, needing
    // `subst_top(fam,a)`'s own substitution to correctly produce
    // `Id(A,a0,a0)` for `refl(a0)` to check against.
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0));
    let a0_pos = p.push(p.get(a_pos));
    let a_ref = p.get(a_pos);
    let a0_ref = p.get(a0_pos);

    // fam := Id(A, Var(0), a0), one binder deeper than A (the tag x)
    let fam = id(shift(&a_ref, 0, 1), var(0), shift(&a0_ref, 0, 1));
    let sig_ty = sigma(a_ref, fam.clone());
    let target = pair(fam, a0_ref.clone(), refl(a0_ref));
    p.check(&target, &sig_ty).expect("pair(fam, a0, refl(a0)) : Sigma(A, fam)");
}

#[test]
fn pair_with_a_mismatched_second_component_is_rejected() {
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0));
    let a0_pos = p.push(p.get(a_pos));
    let b_pos = p.push(sort(0));

    let a0_ref = p.get(a0_pos);
    let b_ref = p.get(b_pos);
    let fam = shift(&b_ref, 0, 1); // \_:A. B
    // second component should be B-typed, not A-typed
    let bad = pair(fam, a0_ref.clone(), a0_ref);
    assert!(p.infer(&bad).is_err(), "pair's own second component must check against fam(a), not anything else");
}

/// The soundness gate `infer`'s own `WRec` case now needs (see
/// `Expr::WRec`'s own doc): a term whose `children_ty` field doesn't
/// match `target`'s own real children-type family must be rejected
/// outright, not silently trusted. Without this check, `whnf_impl`
/// would honestly (per its own, now-correct reduction rule) type an
/// induction-hypothesis closure at whatever *wrong* domain a
/// maliciously- or accidentally-constructed `children_ty` names --
/// letting a step function's own body get away with treating that
/// closure's argument as something it isn't.
#[test]
fn wrec_with_a_mismatched_children_ty_is_rejected() {
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0)); // A : Type0
    let a0_pos = p.push(p.get(a_pos)); // a0 : A
    let bc_pos = p.push(sort(0)); // Bc : Type0
    let w_ty_pre = wty(p.get(a_pos), shift(&p.get(bc_pos), 0, 1));
    let f0_pos = p.push(arrow(p.get(bc_pos), w_ty_pre));

    let a_ref = p.get(a_pos);
    let bc_ref = p.get(bc_pos);
    let w_ty = wty(a_ref.clone(), shift(&bc_ref, 0, 1));
    let target = sup(p.get(a0_pos), p.get(f0_pos));
    let motive = lam(w_ty.clone(), shift(&w_ty, 0, 1));
    let f_ty_d1 = pi(shift(&bc_ref, 0, 1), shift(&w_ty, 0, 2));
    let ih_ty_d2 = pi(shift(&bc_ref, 0, 2), app(shift(&motive, 0, 3), app(var(1), var(0))));
    let step = lam(a_ref, lam(f_ty_d1, lam(ih_ty_d2, sup(var(2), var(1)))));

    // The real, matching children_ty (`shift(&bc_ref, 0, 1)`) is
    // exactly what `w_recursor_computes_definitionally` above uses,
    // and typechecks fine -- substituted here for a wrong one
    // (`Sort(0)`, `Bc`'s own type, one universe too high to even be
    // `def_eq` to `Bc` itself) that names the wrong children family.
    let wrong = wrec(motive, sort(0), step, target);
    assert!(
        p.infer(&wrong).is_err(),
        "a WRec term whose children_ty doesn't match target's own real children-type should be rejected, not silently trusted"
    );
}

#[test]
fn j_proves_symmetry_of_id() {
    // sym : Pi A:Type0. Pi x y:A. Id A x y -> Id A y x
    // sym = \A x y p. J(motive = \x y _. Id A y x, base = \x. refl x, x, y, p)
    //
    // Depths while building the body (A=d1,x=d2,y=d3,p=d4; at d4:
    // A=Var3, x=Var2, y=Var1, p=Var0).
    let motive = lam(
        var(3), // A, at d4 (motive's own binder x' sits at d4)
        lam(
            var(4), // A, at d5 (one more binder, y', intervened)
            lam(
                id(var(5), var(1), var(0)), // Id A x' y', at d6
                id(var(6), var(1), var(2)), // Id A y' x', at d7 (swapped)
            ),
        ),
    );
    let base = lam(var(3), refl(var(0))); // \x:A. refl x, at d4

    let sym = lam(
        sort(0),
        lam(
            var(0),
            lam(
                shift(&var(0), 0, 1),
                lam(
                    id(shift(&var(0), 0, 2), var(1), var(0)),
                    jelim(motive, base, var(2), var(1), var(0)),
                ),
            ),
        ),
    );

    let ty = typecheck(&sym).unwrap();
    let expected = pi(
        sort(0),
        pi(
            var(0),
            pi(
                shift(&var(0), 0, 1),
                arrow(
                    id(shift(&var(0), 0, 2), var(1), var(0)),
                    id(shift(&var(0), 0, 2), var(0), var(1)),
                ),
            ),
        ),
    );
    assert!(def_eq(&ty, &expected), "got {ty:?}\nexpected {expected:?}");

    // Sanity: sym A a a (refl a) reduces to refl a, for a postulated A/a.
    let mut p = Postulates::new();
    let a_pos = p.push(sort(0));
    let a0_pos = p.push(p.get(a_pos));
    let a_ty = p.get(a_pos);
    let a0 = p.get(a0_pos);
    let applied = app(
        app(app(app(sym.clone(), a_ty), a0.clone()), a0.clone()),
        refl(a0.clone()),
    );
    assert_eq!(nf(&applied), nf(&refl(a0)));
}

#[test]
fn sym_typechecks_and_flips_the_equality() {
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let a_pos = p.push(p.get(a_ty_pos));
    let b_pos = p.push(p.get(a_ty_pos));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(a_pos), p.get(b_pos)));

    let a_ty = p.get(a_ty_pos);
    let a = p.get(a_pos);
    let b = p.get(b_pos);
    let p1 = p.get(p1_pos);

    let flipped = sym(&a_ty, &a, &b, p1);
    p.check(&flipped, &id(a_ty, b, a)).expect("sym(x,y,p) : Id(A, y, x)");
}

#[test]
fn transport_moves_a_value_across_a_propositional_type_equality() {
    // Postulate two Sort(0)-level types A, B, a proof p : Id(Sort0,A,B),
    // and a : A -- transport(p, a) should typecheck at B.
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let b_ty_pos = p.push(sort(0));
    let p_pos = p.push(id(sort(0), p.get(a_ty_pos), p.get(b_ty_pos)));
    let a_pos = p.push(p.get(a_ty_pos));

    let a_ty = p.get(a_ty_pos);
    let b_ty = p.get(b_ty_pos);
    let proof = p.get(p_pos);
    let a = p.get(a_pos);

    let moved = transport(0, a_ty, b_ty.clone(), proof, a);
    p.check(&moved, &b_ty).expect("transport(p,a) : B");
}

#[test]
fn transport_along_refl_is_the_identity() {
    // p = refl A : Id(Sort0,A,A) -- transport should reduce to `a`
    // itself definitionally (the base case of J is the identity fn).
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let a_pos = p.push(p.get(a_ty_pos));

    let a_ty = p.get(a_ty_pos);
    let a = p.get(a_pos);

    let moved = transport(0, a_ty.clone(), a_ty.clone(), refl(a_ty.clone()), a.clone());
    assert_eq!(nf(&moved), nf(&a), "transport along refl should compute to the identity");
}

#[test]
fn cong1_and_trans_typecheck_and_compose() {
    // Postulate A, a, b, c and proofs p1:Id(A,a,b), p2:Id(A,b,c), plus
    // a function f:A->A, then check cong1/trans against their expected
    // types and that they chain: trans(cong1(f,a,b,p1), cong1(f,b,c,p2))
    // : Id(A, f a, f c).
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let a_pos = p.push(p.get(a_ty_pos));
    let b_pos = p.push(p.get(a_ty_pos));
    let c_pos = p.push(p.get(a_ty_pos));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(a_pos), p.get(b_pos)));
    let p2_pos = p.push(id(p.get(a_ty_pos), p.get(b_pos), p.get(c_pos)));
    let f_pos = p.push(arrow(p.get(a_ty_pos), p.get(a_ty_pos)));

    let a_ty = p.get(a_ty_pos);
    let a = p.get(a_pos);
    let b = p.get(b_pos);
    let c = p.get(c_pos);
    let p1 = p.get(p1_pos);
    let p2 = p.get(p2_pos);
    let f = p.get(f_pos);

    let c1 = cong1(&a_ty, &a_ty, &f, a.clone(), b.clone(), p1);
    p.check(&c1, &id(a_ty.clone(), app(f.clone(), a.clone()), app(f.clone(), b.clone())))
        .expect("cong1(f,a,b,p1) : Id(A, f a, f b)");

    let c2 = cong1(&a_ty, &a_ty, &f, b.clone(), c.clone(), p2);
    p.check(&c2, &id(a_ty.clone(), app(f.clone(), b.clone()), app(f.clone(), c.clone())))
        .expect("cong1(f,b,c,p2) : Id(A, f b, f c)");

    let chained = trans_proof(&a_ty, &app(f.clone(), a.clone()), &app(f.clone(), b.clone()), &app(f.clone(), c.clone()), c1, c2);
    p.check(&chained, &id(a_ty, app(f.clone(), a), app(f, c)))
        .expect("trans(cong1(..p1), cong1(..p2)) : Id(A, f a, f c)");
}

#[test]
fn cong1_with_a_different_codomain_than_domain_typechecks() {
    // f : A -> B (B distinct from A) -- every prior caller of cong1/
    // cong_n happened to have f's codomain equal its domain, so this
    // exercises the b_ty-distinct-from-a_ty case on its own for the
    // first time. cong1(f,a,b,p) : Id(B, f a, f b), not Id(A, ..).
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let b_ty_pos = p.push(sort(0));
    let a_pos = p.push(p.get(a_ty_pos));
    let b_pos = p.push(p.get(a_ty_pos));
    let f_pos = p.push(arrow(p.get(a_ty_pos), p.get(b_ty_pos)));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(a_pos), p.get(b_pos)));

    let a_ty = p.get(a_ty_pos);
    let b_ty = p.get(b_ty_pos);
    let a = p.get(a_pos);
    let b = p.get(b_pos);
    let f = p.get(f_pos);
    let p1 = p.get(p1_pos);

    let c1 = cong1(&a_ty, &b_ty, &f, a.clone(), b.clone(), p1);
    p.check(&c1, &id(b_ty, app(f.clone(), a), app(f, b))).expect("cong1(f,a,b,p1) : Id(B, f a, f b)");
}

#[test]
fn cong_n_with_a_different_codomain_than_domain_typechecks() {
    // Same distinction one level up: g : A -> A -> B.
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let b_ty_pos = p.push(sort(0));
    let g_pos = p.push(arrow(p.get(a_ty_pos), arrow(p.get(a_ty_pos), p.get(b_ty_pos))));
    let x0_pos = p.push(p.get(a_ty_pos));
    let y0_pos = p.push(p.get(a_ty_pos));
    let x1_pos = p.push(p.get(a_ty_pos));
    let y1_pos = p.push(p.get(a_ty_pos));
    let p0_pos = p.push(id(p.get(a_ty_pos), p.get(x0_pos), p.get(y0_pos)));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(x1_pos), p.get(y1_pos)));

    let a_ty = p.get(a_ty_pos);
    let b_ty = p.get(b_ty_pos);
    let g = p.get(g_pos);
    let x0 = p.get(x0_pos);
    let y0 = p.get(y0_pos);
    let x1 = p.get(x1_pos);
    let y1 = p.get(y1_pos);
    let p0 = p.get(p0_pos);
    let p1 = p.get(p1_pos);

    let proof = cong_n(&a_ty, &b_ty, &g, &[x0.clone(), x1.clone()], &[y0.clone(), y1.clone()], vec![p0, p1]);
    let expected = id(b_ty, app(app(g.clone(), x0), x1), app(app(g, y0), y1));
    p.check(&proof, &expected).expect("cong_n(g,[x0,x1],[y0,y1],[p0,p1]) : Id(B, g x0 x1, g y0 y1)");
}

#[test]
fn cong_n_typechecks_for_a_binary_function() {
    // Postulate A, a binary g:A->A->A, x0,y0,x1,y1:A and proofs
    // p0:Id(A,x0,y0), p1:Id(A,x1,y1); check cong_n(g,[x0,x1],[y0,y1],[p0,p1])
    // : Id(A, g x0 x1, g y0 y1) -- the n=2 case `proof.rs`'s non-tail-
    // recursion congruence step needs (e.g. for `f(n-1) + f(n-2)`).
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let g_pos = p.push(arrow(p.get(a_ty_pos), arrow(p.get(a_ty_pos), p.get(a_ty_pos))));
    let x0_pos = p.push(p.get(a_ty_pos));
    let y0_pos = p.push(p.get(a_ty_pos));
    let x1_pos = p.push(p.get(a_ty_pos));
    let y1_pos = p.push(p.get(a_ty_pos));
    let p0_pos = p.push(id(p.get(a_ty_pos), p.get(x0_pos), p.get(y0_pos)));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(x1_pos), p.get(y1_pos)));

    let a_ty = p.get(a_ty_pos);
    let g = p.get(g_pos);
    let x0 = p.get(x0_pos);
    let y0 = p.get(y0_pos);
    let x1 = p.get(x1_pos);
    let y1 = p.get(y1_pos);
    let p0 = p.get(p0_pos);
    let p1 = p.get(p1_pos);

    let proof = cong_n(&a_ty, &a_ty, &g, &[x0.clone(), x1.clone()], &[y0.clone(), y1.clone()], vec![p0, p1]);
    let expected = id(a_ty, app(app(g.clone(), x0), x1), app(app(g, y0), y1));
    p.check(&proof, &expected).expect("cong_n(g,[x0,x1],[y0,y1],[p0,p1]) : Id(A, g x0 x1, g y0 y1)");
}

#[test]
fn cong_n_with_swapped_proofs_is_rejected() {
    // Adversarial: does cong_n's own construction actually get caught
    // when misused, or does it silently produce something that
    // typechecks regardless? Same setup as
    // cong_n_typechecks_for_a_binary_function, but pass p0/p1 in the
    // WRONG order (p1, meant for position 1, supplied for position 0
    // and vice versa) -- p1 : Id(A,x1,y1) doesn't witness Id(A,x0,y0)
    // (x0/x1/y0/y1 are four *distinct* postulates, unrelated to each
    // other), so the resulting term's underlying `J` node should be
    // ill-typed, not vacuously accepted.
    let mut p = Postulates::new();
    let a_ty_pos = p.push(sort(0));
    let g_pos = p.push(arrow(p.get(a_ty_pos), arrow(p.get(a_ty_pos), p.get(a_ty_pos))));
    let x0_pos = p.push(p.get(a_ty_pos));
    let y0_pos = p.push(p.get(a_ty_pos));
    let x1_pos = p.push(p.get(a_ty_pos));
    let y1_pos = p.push(p.get(a_ty_pos));
    let p0_pos = p.push(id(p.get(a_ty_pos), p.get(x0_pos), p.get(y0_pos)));
    let p1_pos = p.push(id(p.get(a_ty_pos), p.get(x1_pos), p.get(y1_pos)));

    let a_ty = p.get(a_ty_pos);
    let g = p.get(g_pos);
    let x0 = p.get(x0_pos);
    let y0 = p.get(y0_pos);
    let x1 = p.get(x1_pos);
    let y1 = p.get(y1_pos);
    let p0 = p.get(p0_pos);
    let p1 = p.get(p1_pos);

    // Sanity: correctly-ordered proofs typecheck (mirrors the test above).
    let good = cong_n(
        &a_ty,
        &a_ty,
        &g,
        &[x0.clone(), x1.clone()],
        &[y0.clone(), y1.clone()],
        vec![p0.clone(), p1.clone()],
    );
    let expected = id(a_ty.clone(), app(app(g.clone(), x0.clone()), x1.clone()), app(app(g.clone(), y0.clone()), y1.clone()));
    p.check(&good, &expected).expect("correctly-ordered cong_n should typecheck");

    // Adversarial: swap the proof order.
    let bad = cong_n(&a_ty, &a_ty, &g, &[x0, x1], &[y0, y1], vec![p1, p0]);
    assert!(
        p.check(&bad, &expected).is_err(),
        "cong_n with mismatched (swapped) proofs should be rejected, not silently accepted"
    );
}

/// `open`/`close` wrap exactly the parameters bound inside the scope
/// and roll them back; `abandon` rolls back without closing.
#[test]
fn a_scope_closes_over_what_it_bound_and_rolls_it_back() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    let body = id(p.get(a), x.clone(), x);
    let closed = p.close(s, Binder::Pi, body);
    assert_eq!((p.globals.len(), p.params.len(), p.scopes), (1, 0, 0));
    assert!(p.check(&closed, &sort(0)).is_ok());
    let s = p.open();
    p.bind(p.get(a));
    p.abandon(s);
    assert_eq!((p.globals.len(), p.params.len(), p.scopes), (1, 0, 0));
}

/// Globals are never truncated: a postulate pushed after a scope closed
/// takes the next level, and a scope's `close` never wraps one.
#[test]
fn closing_a_scope_keeps_every_postulate() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    let _ = p.close(s, Binder::Lam, x);
    let b = p.push(sort(0));
    assert_eq!((a, b), (0, 1));
    assert_eq!(p.globals.len(), 2);
}

/// A postulate is `Const(pos)` inside a scope as well as outside one;
/// a scope's parameters are `Free`s.
#[test]
fn postulates_are_consts_and_a_scopes_parameters_are_frees() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    assert_eq!(p.get(a), Expr::Const(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    assert_eq!(p.get(a), Expr::Const(0));
    assert_eq!(x, Expr::Free(0));
    assert!(p.check_open(&x, &p.get(a)).is_ok());
    let closed = p.close(s, Binder::Lam, x);
    assert_eq!(closed, lam(Expr::Const(0), var(0)));
    assert!(p.check(&closed, &pi(Expr::Const(0), Expr::Const(0))).is_ok());
}

#[test]
#[should_panic(expected = "isn't a type")]
fn push_rejects_an_entry_that_isnt_a_type() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let x = p.push(p.get(a));
    p.push(p.get(x)); // x : A is an element, not a type
}

#[test]
#[should_panic(expected = "closed")]
fn push_rejects_a_postulate_with_a_loose_var() {
    let mut p = Postulates::new();
    p.push(sort(0));
    p.push(var(0));
}

#[test]
#[should_panic(expected = "closed")]
fn push_rejects_a_postulate_with_a_free() {
    let mut p = Postulates::new();
    p.push(Expr::Free(0));
}

#[test]
#[should_panic(expected = "unknown constant")]
fn push_rejects_a_forward_const() {
    let mut p = Postulates::new();
    p.push(sort(0));
    p.push(Expr::Const(1)); // its own level
}

/// A parameter's type may mention the scope's earlier parameters, and
/// it's still checked to be a type.
#[test]
fn bind_accepts_a_parameter_typed_by_an_earlier_one() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    p.bind(id(p.get(a), x.clone(), x));
    p.abandon(s);
}

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

/// A push inside a scope survives `abandon` too: `abandon` rolls back
/// bound parameters but not globals, so `globals.len()` is unchanged
/// and the pushed value still type-checks (RELATED_WORK §70, stage 4).
#[test]
fn a_push_inside_a_scope_survives_abandon() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let _x = p.bind(p.get(a));
    let c = p.push(p.get(a));
    assert_eq!(p.globals.len(), 2);
    p.abandon(s);
    assert_eq!(p.globals.len(), 2);
    assert!(p.check(&p.get(c), &p.get(a)).is_ok());
}

/// A push inside a nested scope survives both `close`s, the same way
/// a push in a single scope survives one (RELATED_WORK §70, stage 4).
#[test]
fn a_push_inside_a_nested_scope_survives_both_closes() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let outer = p.open();
    let _x = p.bind(p.get(a));
    let inner = p.open();
    let y = p.bind(p.get(a));
    let c = p.push(p.get(a));
    let inner_closed = p.close(inner, Binder::Pi, id(p.get(a), y, p.get(c)));
    let closed = p.close(outer, Binder::Pi, inner_closed);
    assert_eq!(closed, pi(Expr::Const(0), pi(Expr::Const(0), id(Expr::Const(0), var(0), Expr::Const(1)))));
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

/// Closing over a bound parameter with `Pi` builds a type and with
/// `Lam` a value of it: `\x:A. refl x : Pi x:A. Id(A,x,x)`.
#[test]
fn closing_with_lam_builds_a_value_of_the_pi_closed_type() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));

    let s = p.open();
    let x = p.bind(p.get(a));
    let ty = p.close(s, Binder::Pi, id(p.get(a), x.clone(), x));

    let s = p.open();
    let x = p.bind(p.get(a));
    let value = p.close(s, Binder::Lam, refl(x));

    p.check(&value, &ty).expect("\\x:A. refl x : Pi x:A. Id(A,x,x)");
}

/// The spec's stage 3 test: closing over `Free`s gives exactly the
/// hand-built dependent `Pi` chain.
#[test]
fn close_over_frees_matches_hand_built_dependent_pi_chain() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    let y = p.bind(p.get(a));
    let closed = p.close(s, Binder::Pi, id(p.get(a), x, y));
    assert_eq!(closed, pi(Expr::Const(0), pi(Expr::Const(0), id(Expr::Const(0), var(1), var(0)))));
    assert!(p.check(&closed, &sort(0)).is_ok());
}

/// A scope that binds nothing has no `Free`s to abstract: `close`
/// returns `body` unchanged, for either binder. Exercises
/// `params_and_close_typed`'s own inner scope for a base-case leaf with
/// no self-calls (`no_closures(0)`, proof.rs).
#[test]
fn close_of_an_empty_scope_returns_the_body_unchanged() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let body = p.get(a);

    let s = p.open();
    let closed = p.close(s, Binder::Pi, body.clone());
    assert_eq!(closed, body);

    let s = p.open();
    let closed = p.close(s, Binder::Lam, body.clone());
    assert_eq!(closed, body);
}

/// A later parameter's type mentioning an earlier one becomes a `Var`
/// in its binder's domain.
#[test]
fn close_abstracts_a_parameter_in_a_later_parameters_type() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    let e = p.bind(id(p.get(a), x.clone(), x));
    let closed = p.close(s, Binder::Lam, e);
    assert_eq!(closed, lam(Expr::Const(0), lam(id(Expr::Const(0), var(0), var(0)), var(0))));
}

/// The teeth of "levels are never reused": a `Free` that escapes its
/// scope is left alone by a later scope's `close` and fails the check.
/// With reuse, the later scope would bind it silently.
#[test]
fn a_free_that_escapes_its_scope_is_left_by_a_later_close_and_rejected() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let leaked = p.bind(p.get(a));
    let _ = p.close(s, Binder::Lam, leaked.clone());
    let s = p.open();
    let _y = p.bind(p.get(a));
    let closed = p.close(s, Binder::Lam, leaked);
    let r = p.check(&closed, &pi(Expr::Const(0), Expr::Const(0)));
    assert!(matches!(r, Err(ref e) if e.contains("escaped its scope")), "{r:?}");
}

/// `close`/`abandon` require the innermost scope to close first: closing
/// an outer scope while an inner one is still open panics.
#[test]
#[should_panic(expected = "scopes must close innermost-first")]
fn closing_a_scope_out_of_order_panics() {
    let mut p = Postulates::new();
    let outer = p.open();
    let _inner = p.open();
    let _ = p.close(outer, Binder::Lam, sort(0));
}

/// An inner scope's `close` leaves the outer scope's parameters free.
#[test]
fn an_inner_close_leaves_outer_parameters_free() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let outer = p.open();
    let x = p.bind(p.get(a));
    let inner = p.open();
    let y = p.bind(p.get(a));
    let inner_closed = p.close(inner, Binder::Lam, id(p.get(a), x.clone(), y));
    assert_eq!(inner_closed, lam(Expr::Const(0), id(Expr::Const(0), x, var(0))));
    let closed = p.close(outer, Binder::Lam, inner_closed);
    assert_eq!(closed, lam(Expr::Const(0), lam(Expr::Const(0), id(Expr::Const(0), var(1), var(0)))));
    // The body is a type, so the closed `Lam` is a type family.
    assert!(p.check(&closed, &pi(Expr::Const(0), pi(Expr::Const(0), sort(0)))).is_ok());
}

#[test]
fn check_open_types_the_live_parameters() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    assert!(p.check(&x, &p.get(a)).is_err()); // the kernel rejects Free
    assert!(p.check_open(&x, &p.get(a)).is_ok());
    assert!(p.check_open(&refl(x.clone()), &id(p.get(a), x.clone(), x)).is_ok());
    p.abandon(s);
}

#[test]
#[should_panic(expected = "isn't a type")]
fn bind_rejects_a_type_that_isnt_one() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let _s = p.open();
    let x = p.bind(p.get(a));
    p.bind(x);
}

#[test]
#[should_panic(expected = "bind outside a scope")]
fn bind_panics_outside_a_scope() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    p.bind(p.get(a));
}

/// A parameter whose type mentions an earlier one is looked up at the
/// right depth.
#[test]
fn check_open_types_a_parameter_in_a_dependent_context() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    let e = p.bind(id(p.get(a), x.clone(), x.clone()));
    assert_eq!(p.check_open(&e, &id(p.get(a), x.clone(), x)), Ok(()));
    p.abandon(s);
}

/// Nodes in `e` counted once per allocation, as `proof.rs`'s tests
/// count them.
fn dag_size(e: &Expr) -> usize {
    fn go(e: &Expr, seen: &mut HashSet<*const Expr>) -> usize {
        let mut n = 1;
        same_shape(e, e, |p, _| {
            if seen.insert(Rc::as_ptr(p)) {
                n += go(p, seen);
            }
            true
        });
        n
    }
    go(e, &mut Default::default())
}

/// `d(k+1) = f d(k) d(k)` over a parameter, 30 levels deep: a
/// billion leaves as a tree, 91 nodes as a DAG. Without its memo
/// `close` walked and copied the tree.
#[test]
fn close_is_linear_in_the_dag_of_a_shared_body() {
    const DEPTH: usize = 30;
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let f = p.push(arrow(p.get(a), arrow(p.get(a), p.get(a))));
    let s = p.open();
    let mut d = Rc::new(p.bind(p.get(a)));
    for _ in 0..DEPTH {
        d = Rc::new(Expr::App(Rc::new(Expr::App(Rc::new(p.get(f)), d.clone())), d));
    }
    let t = std::time::Instant::now();
    let closed = p.close(s, Binder::Lam, (*d).clone());
    let took = t.elapsed();
    assert!(took < std::time::Duration::from_millis(50), "took {took:?}");
    // The Lam, its domain, the base `Var`, and 3 nodes per level.
    assert_eq!(dag_size(&closed), 3 * DEPTH + 3);
    assert!(p.check(&closed, &arrow(p.get(a), p.get(a))).is_ok());
}
