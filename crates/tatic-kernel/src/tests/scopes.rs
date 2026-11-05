use super::*;

/// `open`/`close` wrap exactly the parameters bound inside the scope
/// and roll them back; `abandon` rolls back without closing.
#[test]
fn a_scope_closes_over_what_it_bound_and_rolls_it_back() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    let body = id(p.get(a), x, x);
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
    assert_eq!(p.get(a), mk(Node::Const(0)));
    let s = p.open();
    let x = p.bind(p.get(a));
    assert_eq!(p.get(a), mk(Node::Const(0)));
    assert_eq!(x, mk(Node::Free(0)));
    assert!(p.check_open(&x, &p.get(a)).is_ok());
    let closed = p.close(s, Binder::Lam, x);
    assert_eq!(closed, lam(mk(Node::Const(0)), var(0)));
    assert!(p.check(&closed, &pi(mk(Node::Const(0)), mk(Node::Const(0)))).is_ok());
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
    p.push(mk(Node::Free(0)));
}

#[test]
#[should_panic(expected = "unknown constant")]
fn push_rejects_a_forward_const() {
    let mut p = Postulates::new();
    p.push(sort(0));
    p.push(mk(Node::Const(1))); // its own level
}

/// A parameter's type may mention the scope's earlier parameters, and
/// it's still checked to be a type.
#[test]
fn bind_accepts_a_parameter_typed_by_an_earlier_one() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    p.bind(id(p.get(a), x, x));
    p.abandon(s);
}

/// A push inside a scope adds a global: `close` doesn't wrap it, and
/// the closed term refers to it by `Const` (docs/related-work/ §70, stage 4).
#[test]
fn a_push_inside_a_scope_is_a_global_that_close_leaves_alone() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    let c = p.push(p.get(a));
    let closed = p.close(s, Binder::Pi, id(p.get(a), x, p.get(c)));
    assert_eq!(closed, pi(mk(Node::Const(0)), id(mk(Node::Const(0)), var(0), mk(Node::Const(1)))));
    assert!(p.check(&closed, &sort(0)).is_ok());
    assert_eq!(p.globals.len(), 2);
}

/// A push inside a scope survives `abandon` too: `abandon` rolls back
/// bound parameters but not globals, so `globals.len()` is unchanged
/// and the pushed value still type-checks (docs/related-work/ §70, stage 4).
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
/// a push in a single scope survives one (docs/related-work/ §70, stage 4).
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
    assert_eq!(closed, pi(mk(Node::Const(0)), pi(mk(Node::Const(0)), id(mk(Node::Const(0)), var(0), mk(Node::Const(1))))));
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
    p.push(id(p.get(a), x, x));
}

/// Closing over a bound parameter with `Pi` builds a type and with
/// `Lam` a value of it: `\x:A. refl x : Pi x:A. Id(A,x,x)`.
#[test]
fn closing_with_lam_builds_a_value_of_the_pi_closed_type() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));

    let s = p.open();
    let x = p.bind(p.get(a));
    let ty = p.close(s, Binder::Pi, id(p.get(a), x, x));

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
    assert_eq!(closed, pi(mk(Node::Const(0)), pi(mk(Node::Const(0)), id(mk(Node::Const(0)), var(1), var(0)))));
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
    let closed = p.close(s, Binder::Pi, body);
    assert_eq!(closed, body);

    let s = p.open();
    let closed = p.close(s, Binder::Lam, body);
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
    let e = p.bind(id(p.get(a), x, x));
    let closed = p.close(s, Binder::Lam, e);
    assert_eq!(closed, lam(mk(Node::Const(0)), lam(id(mk(Node::Const(0)), var(0), var(0)), var(0))));
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
    let _ = p.close(s, Binder::Lam, leaked);
    let s = p.open();
    let _y = p.bind(p.get(a));
    let closed = p.close(s, Binder::Lam, leaked);
    let r = p.check(&closed, &pi(mk(Node::Const(0)), mk(Node::Const(0))));
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
    let inner_closed = p.close(inner, Binder::Lam, id(p.get(a), x, y));
    assert_eq!(inner_closed, lam(mk(Node::Const(0)), id(mk(Node::Const(0)), x, var(0))));
    let closed = p.close(outer, Binder::Lam, inner_closed);
    assert_eq!(closed, lam(mk(Node::Const(0)), lam(mk(Node::Const(0)), id(mk(Node::Const(0)), var(1), var(0)))));
    // The body is a type, so the closed `Lam` is a type family.
    assert!(p.check(&closed, &pi(mk(Node::Const(0)), pi(mk(Node::Const(0)), sort(0)))).is_ok());
}

#[test]
fn check_open_types_the_live_parameters() {
    let mut p = Postulates::new();
    let a = p.push(sort(0));
    let s = p.open();
    let x = p.bind(p.get(a));
    assert!(p.check(&x, &p.get(a)).is_err()); // the kernel rejects Free
    assert!(p.check_open(&x, &p.get(a)).is_ok());
    assert!(p.check_open(&refl(x), &id(p.get(a), x, x)).is_ok());
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
    let e = p.bind(id(p.get(a), x, x));
    assert_eq!(p.check_open(&e, &id(p.get(a), x, x)), Ok(()));
    p.abandon(s);
}

/// `d(k+1) = f d(k) d(k)` over a parameter, `n` levels deep: 2^n
/// leaves as a tree, 2n + 4 nodes as a DAG. Without its memo `close`
/// walked and copied the tree.
#[test]
fn close_is_linear_in_the_dag_of_a_shared_body() {
    assert_scales("close", 10, 20, 8, TIMER_NOISE, |n| {
        let mut p = Postulates::new();
        let a = p.push(sort(0));
        let f = p.push(arrow(p.get(a), arrow(p.get(a), p.get(a))));
        let s = p.open();
        let d = (0..n).fold(p.bind(p.get(a)), |d, _| app(app(p.get(f), d), d));
        let mut closed = None;
        let took = timed(|| closed = Some(p.close(s, Binder::Lam, d)));
        let closed = closed.unwrap();
        // The Lam, its domain, the base `Var`, the one `f` node, and 2 `App`s per level.
        assert_eq!(term_sizes(&closed).0, 2 * n as usize + 4);
        assert!(p.check(&closed, &arrow(p.get(a), p.get(a))).is_ok());
        took
    });
}

/// `scoped` escapes its result only in the call that opened the scope, and a panic inside it still closes the scope.
#[test]
fn scoped_escapes_only_when_outermost() {
    struct Count(std::rc::Rc<std::cell::Cell<u32>>);
    impl Escape for Count {
        fn escape(self) -> Self {
            self.0.set(self.0.get() + 1);
            self
        }
    }
    let n = std::rc::Rc::new(std::cell::Cell::new(0));
    let _c = scoped(|| {
        assert_ne!(intern_generation(), 0, "scoped switches the table on");
        let inner = scoped(|| Count(n.clone()));
        assert_eq!(n.get(), 0, "a nested scoped escapes nothing");
        inner
    });
    assert_eq!((n.get(), intern_generation()), (1, 0));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| scoped(|| -> () { panic!("inside scoped") })));
    assert!(r.is_err());
    assert_eq!(intern_generation(), 0, "a panic closes the scope");
    let _d = scoped(|| Count(n.clone()));
    assert_eq!(n.get(), 2, "after a panic, the next scoped opens the scope again");
}

/// A handle used after the region it was built in closed panics instead of naming another term (spec, "Soundness" 2).
#[test]
#[should_panic(expected = "dead handle")]
fn a_handle_from_a_closed_region_is_dead() {
    let kept = std::cell::Cell::new(None);
    scoped(|| kept.set(Some(app(var(0), var(1)))));
    let e = kept.get().unwrap();
    let _ = e.node();
}

/// `Debug` on a dead handle reports it instead of panicking, so an `assert_eq!` that prints one still says what failed.
#[test]
fn a_dead_handle_prints_as_dead() {
    let kept = std::cell::Cell::new(None);
    scoped(|| kept.set(Some(app(var(0), var(1)))));
    assert_eq!(format!("{:?}", kept.get().unwrap()), "<dead handle>");
}
