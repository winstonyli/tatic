use super::*;

/// A term's cached range is one more than its largest free variable,
/// as a walk of the whole term finds it (0 when closed). The
/// pool's variables are below 4 and binders only lower them, so
/// checking indices below 8 covers every one that can occur.
/// A DAG whose tree is 2^60 nodes prints as about 400 characters, at once (doc section 82).
#[test]
fn brief_bounds_the_text_of_an_exponential_tree() {
    let tree = |n| (0..n).fold(sort(0), |e, _| app(e, e));
    let text = brief(&tree(60));
    assert!(text.len() <= 400 + 4, "{} chars", text.len());
    assert!(text.ends_with(" ..."));
    // 2^10 leaves already overflow the text.
    assert_scales("brief", 10, 60, 30, TIMER_NOISE, move |n| {
        let e = tree(n);
        timed(|| {
            brief(&e);
        })
    });
    assert_eq!(brief(&sort(3)), "Type3");
}

#[test]
fn loose_matches_a_walk() {
    let mut next = splitmix(11);
    for _ in 0..20_000 {
        let e = random_term(&mut next);
        let walk = (0..8u32).rev().find(|&i| is_var_free_ref(&e, i)).map_or(0, |i| i + 1);
        assert_eq!(e.loose(), walk, "{e:?}");
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

/// Inside an interning scope a `whnf` found by one `def_eq` stays in the table for the next; outside
/// one nothing is kept.
#[test]
fn whnf_memo_outlives_one_def_eq_in_a_scope() {
    let redex = || app(lam(sort(0), var(0)), var(7));
    assert!(def_eq(&app(var(5), redex()), &app(var(5), var(7))));
    assert_eq!(hc_whnf_get(&redex()), None);
    scoped(|| {
        let x = redex();
        assert_eq!(hc_whnf_get(&x), None);
        assert!(def_eq(&app(var(5), x), &app(var(5), var(7))));
        assert_eq!(hc_whnf_get(&x), Some(var(7)));
    })
}

/// `brief_nf` prints what `brief(&nf(..))` prints, and reduces only the part it prints: the normal
/// form of the Church numeral `16 4` has 4^16 nested applications.
#[test]
fn brief_nf_normalizes_only_what_it_prints() {
    // c(k) = \f x. f^k x
    let num = |k: usize| lam(sort(0), lam(var(0), (0..k).fold(var(0), |x, _| app(var(1), x))));
    let small = [app(num(2), num(2)), id(sort(1), app(num(3), num(2)), num(1)), pi(app(lam(sort(1), var(0)), sort(0)), var(0))];
    for e in &small {
        assert_eq!(brief_nf(e), brief(&nf(e)));
    }
    let big = brief_nf(&app(num(16), num(4)));
    assert!(big.ends_with(" ...") && big.contains(&"(#1 ".repeat(40)), "{big}");
}

/// A closed function value applied at several places to different arguments is reduced once:
/// `b(i+1) = \C x y. b(i) C (b(i) C y x) (b(i) C x y)`, with `b(i)` one shared node, calls `b(i)`
/// twice per level, so reducing `b(30)` as a tree takes 2^30 steps (outside a scope and inside one).
#[test]
fn closed_function_values_are_reduced_once() {
    const DEPTH: usize = 30;
    let tt = lam(sort(0), lam(var(0), lam(var(1), var(1))));
    let ff = lam(sort(0), lam(var(0), lam(var(1), var(0))));
    let build = || {
        let mut b = tt;
        for _ in 0..DEPTH {
            // `b C p q`, keeping `b` the shared node
            let call = |p: Expr, q: Expr| app(app(app(b, var(2)), p), q);
            let body = call(call(var(0), var(1)), call(var(1), var(0)));
            b = lam(sort(0), lam(var(0), lam(var(1), body)));
        }
        b
    };
    // b(i) is ff for every i >= 1
    assert!(def_eq(&build(), &ff) && !def_eq(&build(), &tt));
    scoped(|| {
        assert!(def_eq(&build(), &ff) && !def_eq(&build(), &tt));
    })
}

/// `cong_n` outside an interning scope still shares its shifted copies of `f`: with `f` a DAG of
/// `d(k+1) = v1 d(k) d(k)` over a loose variable, a copy shifted as a tree would have 2^20 nodes.
#[test]
fn cong_n_shares_shifted_copies_outside_a_scope() {
    const DEPTH: usize = 20;
    assert_eq!(intern_generation(), 0);
    let mut d = var(0);
    for _ in 0..DEPTH {
        d = app(app(var(1), d), d);
    }
    let xs = [var(2), var(3)];
    let ps = vec![refl(var(2)), refl(var(3))];
    let proof = cong_n(&sort(0), &sort(0), &d, &xs, &xs, ps);
    assert!(term_sizes(&proof).0 < 30 * DEPTH, "{}", term_sizes(&proof).0);
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
        let mut body = e;
        for _ in 1..m {
            body = lam(sort(0), body);
        }
        let mut cur = body;
        for (i, a) in args.iter().enumerate() {
            let next_body = instantiate_ref(&cur, a, 0);
            cur = if i + 1 < m {
                match next_body.node() {
                    Node::Lam(_, b) => b,
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

/// The same inside one interning scope, with arguments drawn from a small pool so that lists share
/// suffixes and the memo answers across them.
#[test]
fn instantiate_n_matches_sequential_substitution_in_a_scope() {
    scoped(|| {
        let mut next = splitmix(43);
        let pool: Vec<Expr> = (0..4).map(|_| random_term(&mut next)).collect();
        let rcs: Vec<Expr> = pool.iter().map(|a| mk(a.node())).collect();
        // Each term meets several lists, so the memo (keyed by node address) answers across them.
        let mut e = random_term(&mut next);
        for i in 0..20_000 {
            if i % 10 == 0 {
                e = random_term(&mut next);
            }
            let m = 1 + next() % 3;
            let pick: Vec<usize> = (0..m).map(|_| next() % 4).collect();
            let mut cur = e;
            for _ in 1..m {
                cur = lam(sort(0), cur);
            }
            for (i, &p) in pick.iter().enumerate() {
                let next_body = instantiate_ref(&cur, &pool[p], 0);
                cur = if i + 1 < m {
                    match next_body.node() {
                        Node::Lam(_, b) => b,
                        other => panic!("lost the inner lambda: {other:?}"),
                    }
                } else {
                    next_body
                };
            }
            let refs: Vec<&Expr> = pick.iter().map(|&p| &rcs[p]).collect();
            assert_eq!(instantiate_n(&e, &refs, 0), cur, "e {e:?}, pick {pick:?}");
        }
    })
}

/// A child with nothing to change comes back as the same node, not a
/// copy: a closed one always, and an open one when its variables are
/// all below the cutoff or depth.
#[test]
fn shift_keeps_closed_children_by_pointer() {
    let closed = pi(sort(0), var(0));
    let e = app(closed, var(0));
    let shifted = shift(&e, 0, 1);
    let Node::App(f, a) = shifted.node() else { panic!() };
    assert!(node_key(&f) == node_key(&closed), "shift copied a closed child");
    assert_eq!(a, var(1));
    let instantiated = instantiate(&e, &sort(1), 0);
    let Node::App(f, a) = instantiated.node() else { panic!() };
    assert!(node_key(&f) == node_key(&closed), "instantiate copied a closed child");
    assert_eq!(a, sort(1));

    // Under cutoff 1, `Var(0)` is bound, so its child keeps its pointer
    // and only `Var(2)` moves.
    let low = var(0);
    let e = app(low, var(2));
    let shifted = shift(&e, 1, 1);
    let Node::App(f, a) = shifted.node() else { panic!() };
    assert!(node_key(&f) == node_key(&low), "shift copied a child below the cutoff");
    assert_eq!(a, var(3));
    let instantiated = instantiate(&e, &sort(1), 1);
    let Node::App(f, a) = instantiated.node() else { panic!() };
    assert!(node_key(&f) == node_key(&low), "instantiate copied a child below the depth");
    assert_eq!(a, var(1));

    // A whole term with nothing to change comes back with its children
    // by pointer; check the domain.
    let e = pi(closed, var(0));
    let shifted = shift(&e, 0, 5);
    let Node::Pi(dom, _) = shifted.node() else { panic!() };
    assert!(node_key(&dom) == node_key(&closed));
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
        assert_eq!(e.free(), walk, "{e:?}");
    }
    assert!(with_free > 2_000, "only {with_free} terms had a Free");
}

/// The two new leaves are neutral atoms: each is equal only to itself,
/// and never to the other kind or to a `Var` with the same number.
#[test]
fn const_and_free_are_equal_only_to_themselves() {
    let (c0, c1, f0, f1) = (mk(Node::Const(0)), mk(Node::Const(1)), mk(Node::Free(0)), mk(Node::Free(1)));
    assert!(def_eq(&c0, &mk(Node::Const(0))));
    assert!(def_eq(&f0, &mk(Node::Free(0))));
    for (x, y) in [(&c0, &c1), (&f0, &f1), (&c0, &f0), (&c0, &var(0)), (&f0, &var(0))] {
        assert!(!def_eq(x, y), "{x:?} vs {y:?}");
        assert!(x != y, "{x:?} == {y:?}");
    }
}

/// Beta reduction substitutes for the bound `Var` only: a `Const` or a
/// `Free` in the body, or in the argument, comes through unchanged.
#[test]
fn beta_leaves_const_and_free_alone() {
    let (c0, f1, f3) = (mk(Node::Const(0)), mk(Node::Free(1)), mk(Node::Free(3)));
    let body = app(c0, var(0));
    assert_eq!(whnf(&app(lam(sort(0), c0), sort(0))), c0);
    assert_eq!(whnf(&app(lam(sort(0), body), f3)), app(c0, f3));
    assert_eq!(nf(&app(lam(sort(0), f1), var(5))), f1);
}

/// `subst_top`'s one pass (`RELATED_WORK.md` §53) must give exactly
/// what substituting and then shifting gives, both when the body uses
/// the variable and when it doesn't.
#[test]
fn subst_top_is_substituting_then_shifting() {
    let (mut seed, mut used, mut unused) = (tatic_rng::SplitMix64::new(1), 0, 0);
    for _ in 0..20_000 {
        let body = random_expr(&mut seed, 5);
        let s = random_expr(&mut seed, 3);
        let reference = shift(&subst(&body, 0, &shift(&s, 0, 1)), 0, -1);
        assert_eq!(subst_top(&body, &s), reference,"body {body:?}, s {s:?}");
        if is_var_free(&body, 0) { used += 1 } else { unused += 1 }
    }
    assert!(used > 2_000 && unused > 2_000, "used {used}, unused {unused}");
}

/// The node table returns the same node for an equal key, also after it has grown, and distinct nodes
/// for keys that differ only in the leaf value or the constructor.
#[test]
fn intern_finds_equal_nodes_after_growth() {
    scoped(|| {
        let mut chain = vec![mk(Node::Var(0))];
        for i in 1..10_000 {
            let next = mk(Node::App(chain[i - 1], mk(Node::Var(i as u32 % 7))));
            chain.push(next);
        }
        for n in &chain {
            assert!(node_key(n) == node_key(&mk(n.node())));
        }
        let (a, b) = (mk(Node::Var(1)), mk(Node::Sort(1)));
        assert!(node_key(&a) != node_key(&b) && node_key(&a) != node_key(&mk(Node::Var(2))));
        let (f, x) = (chain[5], chain[6]);
        assert!(node_key(&mk(Node::App(f, x))) != node_key(&mk(Node::Pi(f, x))));
    })
}

/// The `uses` slot fills the node's spare word, and answers as the walk does: a repeated query
/// is answered from the slot, a different one replaces it, and queries too wide for it still work.
#[test]
fn uses_slot_is_free_and_agrees_with_the_walk() {
    scoped(|| {
        let x = lam(var(0), app(var(1), var(3)));
        assert_eq!(with_spaces(|s| s.uses_slot(&x, 0, 2)), None);
        // Outside the binder `x` mentions loose variables 0 and 2.
        for (d, m, want) in [(0, 2, true), (0, 2, true), (1, 1, false), (2, 1, true), (3, 1, false), (1, 1 << 15, true)] {
            assert_eq!(hc_uses(&x, d, m), want, "d={d} m={m}");
            // `uses` answers from `loose` alone, without the slot, when nothing is loose at or above `d`.
            if m < 1 << 15 && x.loose() > d {
                assert_eq!(with_spaces(|s| s.uses_slot(&x, d, m)), Some(want), "d={d} m={m}");
            }
        }
    })
}

/// `uses`'s bounds memo answers as `lowest_loose` does, whatever order the queries come in: wide
/// then narrow queries narrow `hi`, narrow then wide ones raise `lo`.
#[test]
fn uses_bounds_agree_with_lowest_loose() {
    scoped(|| {
        let x = lam(var(0), app(app(var(3), var(7)), lam(var(0), var(6))));
        let mut memo = IdMap::default();
        let mut qs: Vec<(u32, u32)> = (0..8).flat_map(|d| (0..10).map(move |m| (d, m))).collect();
        for round in 0..3 {
            if round == 1 {
                qs.reverse();
            } else if round == 2 {
                qs.sort_by_key(|&(d, m)| (m * 7 + d * 3) % 11);
            }
            for &(d, m) in &qs {
                let want = hc_lowest_loose(&x, d, &mut memo) < m;
                assert_eq!(hc_uses(&x, d, m), want, "round {round} d={d} m={m}");
            }
        }
    })
}

/// A walk's memo stores shared nodes only: `t` (two parents) gets an `inst` and a `lows` entry, `u` (one) neither.
#[test]
fn walk_memos_store_only_shared_nodes() {
    scoped(|| {
        let deep = |a, b| app(app(app(var(0), var(a)), var(b)), var(3));
        let (t, u) = (deep(1, 2), deep(4, 5));
        let body = app(app(t, t), u);
        assert!(t.shared() && !u.shared());
        instantiate_n(&body, &[&sort(0)], 0);
        let mut lows = IdMap::default();
        hc_lowest_loose(&lam(sort(0), body), 0, &mut lows);
        with_spaces(|s| {
            let inst = &s.memos.borrow().inst;
            assert!(inst.keys().any(|k| k.0 == s.key(&t)) && !inst.keys().any(|k| k.0 == s.key(&u)));
            assert!(lows.keys().any(|k| k.0 == s.key(&t)) && !lows.keys().any(|k| k.0 == s.key(&u)));
        });
    })
}

/// The instantiation memo skips nodes at most two levels above their leaves.
#[test]
fn low_is_height_at_most_two() {
    let two = app(app(var(0), var(1)), var(2));
    assert!(hc_low(&var(0)) && hc_low(&app(var(0), var(1))) && hc_low(&two));
    assert!(!hc_low(&app(two, var(3))));
}

/// Lists that fit `args_id`'s stack buffer and lists that don't get stable ids, distinct per list.
#[test]
fn args_id_is_stable_for_short_and_long_lists() {
    scoped(|| {
        let vs: Vec<Expr> = (0..12).map(var).collect();
        let refs: Vec<&Expr> = vs.iter().collect();
        let (short, long) = (&refs[..3], &refs[..12]);
        let (s, l) = (hc_args_id(short), hc_args_id(long));
        assert!(s & LIST_BIT != 0 && l & LIST_BIT != 0);
        assert_ne!(s, l);
        assert_eq!((hc_args_id(short), hc_args_id(long)), (s, l));
        assert_ne!(hc_args_id(&refs[1..4]), s);
    })
}

#[test]
fn subst_top_leaves_an_unused_argument_alone() {
    // n + 1 distinct nodes, 2^n as a tree: copying 2^20 takes about a
    // second in a debug build, and the shortcut doesn't look at it.
    assert_scales("subst_top", 10, 20, 2, 0, |n| {
        let s = (0..n).fold(var(0), |s, _| app(s, s));
        let body = pi(var(3), var(4));
        worked(|| assert_eq!(subst_top(&body, &s), pi(var(2), var(3))))
    });
}

/// Substituting under binders shifts the argument once, where it's used,
/// not again at every binder crossed on the way (`RELATED_WORK.md` §52).
/// Timed against one shift of the argument, so it holds on any machine.
#[test]
fn subst_top_shifts_a_used_argument_once() {
    let mut s = var(0);
    for _ in 0..14 {
        s = app(s, s);
    }
    let depth = 30;
    let mut body = var(depth);
    let mut expected = shift(&s, 0, depth as i32);
    let t = std::time::Instant::now();
    let _ = shift(&s, 0, depth as i32);
    let one_shift_time = t.elapsed();
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

