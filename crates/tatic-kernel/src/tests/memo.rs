use super::*;

/// `d(k+1) = f d(k) d(k)`, 20 levels deep: a million leaves as a
/// tree, 20 shared nodes as a DAG. Without the memo `infer` walked the
/// tree (`RELATED_WORK.md` §63). Postulates as `Const`s, per stage 3.
#[test]
fn infer_is_linear_in_the_dag_of_a_shared_term() {
    assert_scales("infer on a DAG", 10, 20, 3, 0, |n| {
        let mut p = Postulates::new();
        let a_ty = p.push(sort(0));
        p.push(p.get(a_ty));
        p.push(arrow(p.get(a_ty), arrow(p.get(a_ty), p.get(a_ty))));
        p.push(arrow(p.get(a_ty), p.get(a_ty)));
        let d = (0..n).fold(p.get(1), |d, _| app(app(p.get(2), d), d));
        worked(|| assert_eq!(p.infer(&d), Ok(p.get(0))))
    });
}

/// `InferCache::skip` by jump pointers agrees with a walk of `lo` parents on a random context tree,
/// `fresh` binders and the caller's context stopping both, and each jump pointer is the skew-binary one.
#[test]
fn infer_cache_skip_matches_a_parent_walk() {
    let mut next = splitmix(37);
    scoped(|| {
        with_spaces(|s| {
            let mut ic = InferCache::default();
            // Before any binder is entered.
            assert_eq!((ic.skip(0, 0), ic.skip(0, 1)), (Some(0), None));
            let mut ids = vec![0];
            for _ in 0..3000 {
                // Mostly extend a recent context, so runs get deep.
                let c = ids[ids.len() - 1 - next() % ids.len().min(4)];
                ids.push(if next().is_multiple_of(500) { ic.fresh() } else { ic.enter(s, c, &sort((next() % 1_000_000) as u32)) });
            }
            // Some runs start at a `fresh` binder, and some are deep.
            let info = |c: u32| ic.info[c as usize];
            assert!(ids.iter().any(|&c| info(c).run > 0 && info(info(c).parent).loose == u32::MAX));
            assert!(ids.iter().any(|&c| info(c).run > 300));
            for &c in &ids {
                let run = info(c).run;
                // Myers' skew-binary jumps: write `run` greedily as a sum of 2^k - 1; the jump goes out by the
                // smallest term. A wrong jump can still give right answers, only slowly, so check it directly.
                let (mut rest, mut by) = (run, 0);
                while rest > 0 {
                    by = (1 << (31 - (rest + 1).leading_zeros())) - 1;
                    rest -= by;
                }
                assert_eq!(info(c).jump, (0..by).fold(c, |c, _| info(c).parent), "context {c}, run {run}");
                for lo in [0, 1, run.saturating_sub(1), run, run + 1].into_iter().chain((0..4).map(|_| (next() % (run as usize + 1)) as u32)) {
                    let mut walk = Some(c);
                    for _ in 0..lo {
                        walk = walk.filter(|&c| c != 0 && ic.info[c as usize].loose != u32::MAX).map(|c| ic.info[c as usize].parent);
                    }
                    assert_eq!(ic.skip(c, lo), walk, "context {c}, lo {lo}");
                }
            }
        })
    });
}

/// A thread keeps `infer`'s cache between calls but empties it after each: the same shared `Var` under another
/// caller context gets that context's type, not the last call's.
#[test]
fn infer_cache_is_emptied_between_calls() {
    let v = var(0);
    let e = id(sort(0), v.clone(), v);
    assert!(infer(&Ctx::unit(sort(0)), &e).is_ok());
    assert!(infer(&Ctx::unit(sort(1)), &e).is_err(), "a type of the first call's context leaked");
    assert!(infer(&Ctx::unit(sort(0)), &e).is_ok());
}

/// `b(i) = k ((λh:A. b(i+1)) a) ((λh:A→A. b(i+1)) f)`, `n` deep under
/// `λx:A`, with `b(n) = x`. Each shared `b(i+1)` mentions only `x`,
/// but sits under one more binder `h` per level, two types each. A memo
/// key covering every binder down to `x` sees 2^i contexts at level i;
/// skipping the binders below the lowest loose variable sees one. The
/// J motives in `postulates.rs` put shared subterms under unused
/// binders the same way. Finding `b(i+1)`'s lowest loose variable and
/// skipping the `i + 1` binders below it once cost O(i) each, which made
/// the whole check quadratic (`RELATED_WORK.md` §80).
#[test]
fn infer_memo_skips_unused_inner_binders() {
    assert_scales("infer under unused binders", 100, 800, 12, 0, |depth| {
        let mut p = Postulates::new();
        let a_ty = p.push(sort(0));
        let a = p.push(p.get(a_ty));
        let f = p.push(arrow(p.get(a_ty), p.get(a_ty)));
        let k = p.push(arrow(p.get(a_ty), arrow(p.get(a_ty), p.get(a_ty))));
        let mut b = var(depth);
        for _ in 0..depth {
            let under = |ty: Expr, arg: usize| app(lam(ty, b), p.get(arg));
            let (l, r) = (under(p.get(a_ty), a), under(arrow(p.get(a_ty), p.get(a_ty)), f));
            b = app(app(p.get(k), l), r);
        }
        let e = lam(p.get(a_ty), b);
        worked(|| assert_eq!(p.infer(&e), Ok(arrow(p.get(a_ty), p.get(a_ty)))))
    });
}

/// `f a ... a` with `k` arguments, `f : Π x_1 .. x_k : A. Id(A, s, s)`, `s = g x_1 .. x_k`.
/// The codomain mentions every binder, so typing one argument at a time copied the rest of the
/// telescope and of `s` at each, about a million nodes at k = 1,000 (0.64 s in release, 4.6 s in
/// debug); the spine at once copies them once (under 5 ms).
#[test]
fn infer_types_an_application_spine_at_once() {
    assert_scales("infer on a spine", 500, 8000, 24, 0, |k| {
        let mut p = Postulates::new();
        let a_ty = p.push(sort(0));
        let a = p.push(p.get(a_ty));
        let g = p.push((0..k).fold(p.get(a_ty), |t, _| pi(p.get(a_ty), t)));
        let s = (0..k).fold(p.get(g), |s, j| app(s, var(k - 1 - j)));
        let f_ty = (0..k).fold(id(p.get(a_ty), s, s), |t, _| pi(p.get(a_ty), t));
        let f = p.push(f_ty);
        let e = (0..k).fold(p.get(f), |e, _| app(e, p.get(a)));
        let s_a = (0..k).fold(p.get(g), |s, _| app(s, p.get(a)));
        worked(|| assert_eq!(p.infer(&e), Ok(id(p.get(a_ty), s_a, s_a))))
    });
}

/// One node shared under two different binder types has two types.
/// `Pi(Type0, Pi(x, Type0))` is well-typed, `Pi(Type0 -> Type0,
/// Pi(x, Type0))` isn't (`x` is then a function, not a type), and
/// both share the inner `Pi`. A memo keyed on context length would
/// reuse the first's answer for the second and accept.
#[test]
fn infer_memo_keeps_same_length_contexts_apart() {
    let inner = pi(var(0), sort(0));
    let good = pi(sort(0), inner);
    let bad = pi(pi(sort(0), sort(0)), inner);
    assert_eq!(infer(&Ctx::new(), &good), Ok(sort(1)));
    assert!(infer(&Ctx::new(), &id(sort(1), good, bad)).is_err());
}

/// `def_eq` on two right-nested chains `f (f (... x))`, 16,000 deep,
/// that differ only at the bottom. `conv` used to try a structural `==`
/// at every level, each walking down to the bottom again: 23 s in a
/// debug build (`RELATED_WORK.md` §61). `==` is now one id comparison.
#[test]
fn def_eq_is_linear_on_a_chain_that_differs_at_the_bottom() {
    assert_scales("def_eq on chains", 1000, 16000, 24, 0, |n| {
        let chain = |bottom: Expr| (0..n).fold(bottom, |t, _| app(var(0), t));
        let (a, b) = (chain(var(1)), chain(var(2)));
        worked(|| assert!(!def_eq(&a, &b)))
    });
}

/// `work()` counts the same on every run of a query from a fresh thread, and grows with the query, linearly for the chain.
#[test]
fn work_is_deterministic_and_scales_with_the_query() {
    let on_fresh_thread = |n: u32| {
        std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(move || {
                let chain = |bottom: Expr| (0..n).fold(bottom, |t, _| app(var(0), t));
                let (a, b) = (chain(var(1)), chain(var(2)));
                let w0 = work();
                assert!(!def_eq(&a, &b));
                work() - w0
            })
            .unwrap()
            .join()
            .unwrap()
    };
    let (small, again, large) = (on_fresh_thread(1000), on_fresh_thread(1000), on_fresh_thread(2000));
    assert!(small > 0);
    assert_eq!(small, again, "the same query from a fresh thread counts the same");
    assert!(large > small && large < small * 3, "doubling the chain gives {large} against {small}");
}

/// `whnf` keeps each argument's node rather than copying it into
/// a new one: the memos are keyed by node, and a copy used to miss them,
/// so `nf` then normalised the whole argument again at every
/// application (`RELATED_WORK.md` §48).
#[test]
fn whnf_keeps_the_arguments_it_was_given() {
    let x = var(7);
    let y = var(8);
    let same = |got: &[Expr], want: &[&Expr]| {
        got.len() == want.len() && got.iter().zip(want).all(|(g, w)| node_key(g) == node_key(w))
    };

    // A stuck application.
    let stuck = app(app(var(0), var(1)), x);
    assert!(same(&spine_args(&whnf(&stuck))[..1], &[&x]));

    // `J` on `refl` reduces to `base a`.
    let j = jelim(var(0), var(1), x, x, refl(var(9)));
    assert!(same(&spine_args(&whnf(&j)), &[&x]));

    // `SigRec` on a pair reduces to `step a b`.
    let s = sigrec(var(0), var(1), pair(var(2), x, y));
    assert!(same(&spine_args(&whnf(&s)), &[&y, &x]));

    // `WRec` on `sup a f` reduces to `step a f rec`.
    let w = wrec(var(0), var(1), var(2), sup(x, y));
    assert!(same(&spine_args(&whnf(&w))[1..], &[&y, &x]));
}

/// Every recursive traversal `check` reaches -- `infer`, `whnf`
/// (beta-reducing the whole chain), `def_eq`'s `conv`, and
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
                chain = app(id_fn, chain);
            }
            assert!(check(&ctx, &chain, &sort(1)).is_ok());

            // refl^N(Type0) against its own type, and against a wrong one.
            let (mut e, mut ty) = (sort(0), sort(1));
            for _ in 0..N {
                ty = id(ty, e, e);
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

