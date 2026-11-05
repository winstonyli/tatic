use super::*;

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
/// `Node::WRec` level** -- deeper than it first looked, and not a
/// function-extensionality gap (an earlier misdiagnosis, corrected in
/// an earlier commit: funext requires both sides to already be
/// well-typed inhabitants of the same Pi-type before it can relate
/// them, and one side here never was one at all). Proving a
/// `bool_rec`-based step's own result concretely (e.g.
/// `is_zero(Zero) = true`) needs more than one `cong1`/`trans_proof`
/// step, since `bool_rec` is postulated and never auto-reduces on its
/// own -- but building that step used to run into a second, deeper
/// problem underneath: `WRec`'s own automatic reduction (`whnf_in`)
/// built its induction-hypothesis closure with an inert placeholder
/// domain annotation (`sort(0)`) -- harmless for reduction itself
/// (beta substitution never consults a `Lam`'s domain field), but
/// that closure was *unconditionally ill-typed on its own* whenever
/// the step function's `ih` parameter was genuinely used (not just
/// discarded, the way the identity recursor's own step does),
/// blocking it from appearing as a well-typed subterm in any
/// hand-built propositional proof. Fixed now: `Node::WRec` carries an
/// explicit `children_ty` field (`B`, see its own doc) so
/// `whnf_in` can give that closure its *honest* domain
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
    let motive_const = lam(nat_ty_here, shift(&nat_ty_here, 0, 1)); // \_:Nat. Nat

    let f_ty_d1 = pi(wb_here, shift(&nat_ty_here, 0, 2));
    let ih_dom_d2 = shift(&wb_here, 0, 1);
    let ih_body_d3 = app(shift(&motive_const, 0, 3), app(var(1), var(0)));
    let ih_ty_d2 = pi(ih_dom_d2, ih_body_d3);
    let step_id = lam(wa_here, lam(f_ty_d1, lam(ih_ty_d2, sup(var(2), var(1)))));

    let id_on_zero = wrec(motive_const, wb_here, step_id, zero_here);
    p.check(&id_on_zero, &nat_ty_here).expect("id-recursor applied to Zero should typecheck at Nat");
    assert_eq!(nf(&id_on_zero), nf(&zero_here), "the identity recursor should reduce Zero back to Zero");

    let id_on_succ = wrec(motive_const, wb_here, step_id, succ_pred);
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
    let f_ty_for_c_d1 = arrow(wb_here2, shift(&nat_ty_here, 0, 1));
    let ih_dom_d2 = shift(&wb_here2, 0, 1);
    let ih_ty_d2 = arrow(ih_dom_d2, shift(&p.get(nat.bool_pos), 0, 2));
    let c_body_d1 = pi(f_ty_for_c_d1, arrow(ih_ty_d2, shift(&p.get(nat.bool_pos), 0, 2)));
    let is_zero_motive_c = lam(p.get(nat.bool_pos), c_body_d1);

    let f_ty_true = arrow(app(p.get(nat.child_ty_pos), p.get(nat.true_pos)), nat_ty_here);
    let ih_ty_true_d1 = arrow(shift(&app(p.get(nat.child_ty_pos), p.get(nat.true_pos)), 0, 1), shift(&p.get(nat.bool_pos), 0, 1));
    let case_true = lam(f_ty_true, lam(ih_ty_true_d1, shift(&p.get(nat.false_pos), 0, 2)));

    let f_ty_false = arrow(app(p.get(nat.child_ty_pos), p.get(nat.false_pos)), nat_ty_here);
    let ih_ty_false_d1 = arrow(shift(&app(p.get(nat.child_ty_pos), p.get(nat.false_pos)), 0, 1), shift(&p.get(nat.bool_pos), 0, 1));
    let case_false = lam(f_ty_false, lam(ih_ty_false_d1, shift(&p.get(nat.true_pos), 0, 2)));

    let is_zero_step = app(app(app(nat.bool_rec(&p), is_zero_motive_c), case_true), case_false);
    p.check(&is_zero_step, &pi(p.get(nat.bool_pos), app(shift(&is_zero_motive_c, 0, 1), var(0))))
        .expect("is_zero_step : Pi b:Bool. C(b)");

    let is_zero_motive_const = lam(nat_ty_here, shift(&p.get(nat.bool_pos), 0, 1)); // \_:Nat. Bool
    let is_zero_on_zero = wrec(is_zero_motive_const, wb_here2, is_zero_step, zero_here);
    p.check(&is_zero_on_zero, &p.get(nat.bool_pos)).expect("is_zero(Zero) : Bool");

    // The obstacle this test used to demonstrate (see git history: an
    // "inert" placeholder domain, `sort(0)`, made `whnf_in`'s own
    // induction-hypothesis closure unconditionally ill-typed standalone
    // whenever a step genuinely used it) is fixed now: `WRec` carries
    // its own `children_ty` field (`B` from the underlying `W(A,B)`,
    // `infer` cross-checks it against `target`'s own real type -- see
    // `Node::WRec`'s own doc), and `whnf_in` uses `subst_top
    // (children_ty, a)` -- `B(a)`, the true children type at tag `a` --
    // as the closure's own domain instead. This rebuilds *exactly* the
    // closure `whnf_in` now builds internally when reducing
    // `is_zero_on_zero` one step (`is_zero_step` doesn't reduce further
    // on its own -- `bool_rec` is postulated, not a `Lam` -- so this is
    // where `whnf_in`'s own reduction gets stuck, with this exact
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
        honest_domain,
        wrec(shift(&is_zero_motive_const, 0, 1), shift(&wb_here2, 1, 1), shift(&is_zero_step, 0, 1), app(shift(&f_zero_here, 0, 1), var(0))),
    );
    let child_ty_false = app(p.get(nat.child_ty_pos), p.get(nat.false_pos));
    assert!(
        def_eq(&honest_domain, &child_ty_false),
        "subst_top(children_ty, false) should give exactly ChildTy(false), the real children type at the false tag"
    );
    let expected_domain = arrow(child_ty_false, p.get(nat.bool_pos));
    p.check(&rec_step, &expected_domain)
        .expect("with children_ty threaded honestly through whnf_in's own reduction rule, the induction-hypothesis closure now typechecks at its real domain, not just an inert placeholder");

    // Full end-to-end confirmation: `whnf(is_zero_on_zero)` (which
    // internally builds exactly `rec_step` above) itself still
    // typechecks at `Bool` -- the fix doesn't just make the isolated
    // closure well-typed, it keeps the *whole* one-step reduction
    // well-typed too, stuck-on-a-postulate tail and all.
    let stuck_one_step = whnf(&is_zero_on_zero);
    p.check(&stuck_one_step, &p.get(nat.bool_pos)).expect("whnf(is_zero(Zero)) should still typecheck at Bool after the fix");
    assert_eq!(
        stuck_one_step,
        app(app(app(is_zero_step, p.get(nat.false_pos)), f_zero_here), rec_step),
        "whnf_in's own stuck reduction should be exactly is_zero_step(false)(f_zero)(rec_step) -- \
         confirming the hand-rebuilt closure above is the *same* one whnf_in actually produces, \
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
    let is_zero_step_at_false = app(is_zero_step, false_val);
    let c_false_ty = app(is_zero_motive_c, false_val);

    let bfe_inst = app(app(app(nat.bool_rec_false_eq(&p), is_zero_motive_c), case_true), case_false);
    p.check(
        &bfe_inst,
        &id(c_false_ty, is_zero_step_at_false, case_false),
    )
    .expect("bool_rec_false_eq instantiated at (is_zero_motive_c, case_true, case_false) should typecheck");

    // f_cong : C(false) -> Bool := \h. h(f_zero_here)(rec_step)
    let f_cong = lam(c_false_ty, app(app(var(0), shift(&f_zero_here, 0, 1)), shift(&rec_step, 0, 1)));
    let cong_step = cong1(&c_false_ty, &bool_ty, &f_cong, is_zero_step_at_false, case_false, bfe_inst);

    // `refl` bridges `is_zero_on_zero` to its own one-step reduction
    // (definitionally equal, `whnf` being one particular strategy for
    // reaching a shared normal form) -- `trans_proof` then chains that
    // with `cong_step` (whose own type, `Id(Bool, f_cong(is_zero_step
    // (false)), f_cong(case_false))`, is itself definitionally equal
    // to `Id(Bool, stuck_one_step, true)` once both sides beta-reduce,
    // `case_false`'s own body reducing all the way to `true`) to land
    // on the final result.
    let bridge = refl(is_zero_on_zero);
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
    // as the type *by construction* (tatic-kernel's own `infer`, `Expr::
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
        let c_ty = arrow(*bool_ref, sort(1));
        let true_d1 = shift(true_ref, 0, 1);
        let false_d2 = shift(false_ref, 0, 2);
        let pi_cf = pi(app(var(1), false_d2), body_d3);
        let pi_ct = pi(app(var(0), true_d1), pi_cf);
        pi(c_ty, pi_ct)
    }
    // Mirrors `infer`'s own `Node::WRec` case exactly: returns
    // (per-tag body, one binder deep; full `Pi a:wa. ...`).
    fn wrec_step_type(wa: &Expr, wb: &Expr, w_ty0: &Expr, motive: &Expr) -> (Expr, Expr) {
        let f_dom_d1 = *wb;
        let f_ty_d1 = pi(f_dom_d1, shift(w_ty0, 0, 2));
        let ih_dom_d2 = shift(wb, 0, 1);
        let motive_d3 = shift(motive, 0, 3);
        let ih_body_d3 = app(motive_d3, app(var(1), var(0)));
        let ih_ty_d2 = pi(ih_dom_d2, ih_body_d3);
        let motive_d2 = shift(motive, 0, 2);
        let concl_ty_d2 = app(motive_d2, sup(var(1), var(0)));
        let arrow_ty_d2 = pi(ih_ty_d2, shift(&concl_ty_d2, 0, 1));
        let per_tag_body_d1 = pi(f_ty_d1, arrow_ty_d2);
        let full = pi(*wa, per_tag_body_d1);
        (per_tag_body_d1, full)
    }

    let sort_rec_body_d3 = pi(shift(&p.get(nat.bool_pos), 0, 3), app(var(3), var(0)));
    let sort_rec_ty = wrap_c_ct_cf_sort1(&p.get(nat.bool_pos), &p.get(nat.true_pos), &p.get(nat.false_pos), sort_rec_body_d3);
    let sort_rec_pos = p.push(sort_rec_ty);

    // sort_rec_true_eq : Pi C ct cf. Id(C(true), sort_rec(C,ct,cf)(true), ct)
    let true_d3 = shift(&p.get(nat.true_pos), 0, 3);
    let applied_d3 = app(app(app(shift(&p.get(sort_rec_pos), 0, 3), var(2)), var(1)), var(0));
    let true_eq_body_d3 = id(app(var(2), true_d3), app(applied_d3, true_d3), var(1));
    let sort_rec_true_eq_ty = wrap_c_ct_cf_sort1(&p.get(nat.bool_pos), &p.get(nat.true_pos), &p.get(nat.false_pos), true_eq_body_d3);
    let sort_rec_true_eq_pos = p.push(sort_rec_true_eq_ty);

    // sort_rec_false_eq : Pi C ct cf. Id(C(false), sort_rec(C,ct,cf)(false), cf)
    let false_d3 = shift(&p.get(nat.false_pos), 0, 3);
    let applied_d3b = app(app(app(shift(&p.get(sort_rec_pos), 0, 3), var(2)), var(1)), var(0));
    let false_eq_body_d3 = id(app(var(2), false_d3), app(applied_d3b, false_d3), var(0));
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
    let type_motive = lam(nat_ty, sort(0));
    p.check(&type_motive, &arrow(nat_ty, sort(1))).expect("type_motive : Nat -> Sort1");

    let (type_per_tag_d1, type_expected_step_ty) = wrec_step_type(&bool_ty, &wb, &nat_ty, &type_motive);
    let type_motive_c = lam(bool_ty, type_per_tag_d1);

    // Two genuinely distinct Sort0 types to select between -- stand-ins
    // for Clo_1/Clo_2.
    let clo1_ty = nat.unit_ty(&p);
    let clo2_ty = nat_ty;

    let case_true_ty_expected = subst_top(&type_per_tag_d1, &true_val);
    let Node::Pi(f_dom_true, rest_true) = case_true_ty_expected.node() else { panic!("expected Pi") };
    let Node::Pi(ih_dom_true, _) = rest_true.node() else { panic!("expected Pi") };
    let case_true_ty = lam(f_dom_true, lam(ih_dom_true, shift(&clo1_ty, 0, 2)));
    p.check(&case_true_ty, &case_true_ty_expected).expect("case_true_ty : type_motive_c(true)");

    let case_false_ty_expected = subst_top(&type_per_tag_d1, &false_val);
    let Node::Pi(f_dom_false, rest_false) = case_false_ty_expected.node() else { panic!("expected Pi") };
    let Node::Pi(ih_dom_false, _) = rest_false.node() else { panic!("expected Pi") };
    let case_false_ty = lam(f_dom_false, lam(ih_dom_false, shift(&clo2_ty, 0, 2)));
    p.check(&case_false_ty, &case_false_ty_expected).expect("case_false_ty : type_motive_c(false)");

    let type_step = app(app(app(sort_rec, type_motive_c), case_true_ty), case_false_ty);
    p.check(&type_step, &type_expected_step_ty).expect("type_step : Pi b:Bool. type_motive_c(b)");

    // fam := wrec(type_motive, ChildTy(Var0), type_step, Var(0)) --
    // Sigma's own open family body, one binder under the tag.
    let fam = wrec(shift(&type_motive, 0, 1), shift(&wb, 1, 1), shift(&type_step, 0, 1), var(0));

    let sigma_ty = sigma(nat_ty, fam);
    p.check(&sigma_ty, &sort(0)).expect("Sigma(Nat, fam) : Sort0");

    // --- THE KEY CLAIM: Pair(fam, a, b) typechecks for a's tag being a
    // genuinely SYMBOLIC (universally quantified) postulate, not a
    // concrete Sup value -- unlike the earlier tagged-Sigma
    // investigation (RELATED_WORK.md sec 14), which needed `a` concrete.
    let a = p.get(a_pos);

    // value_motive := \x:Nat. fam -- literally reuses `fam` as the
    // Lam's own body, so `value_motive(a)` beta-reduces (unconditionally,
    // for ANY a, symbolic or not) to exactly `subst_top(fam, a)`.
    let value_motive = lam(nat_ty, fam);
    p.check(&value_motive, &arrow(nat_ty, sort(0))).expect("value_motive : Nat -> Sort0");

    let (value_per_tag_d1, value_expected_step_ty) = wrec_step_type(&bool_ty, &wb, &nat_ty, &value_motive);
    let value_motive_c = lam(bool_ty, value_per_tag_d1);

    let value_case_true_expected = subst_top(&value_per_tag_d1, &true_val);
    let Node::Pi(vf_dom_true, vrest_true) = value_case_true_expected.node() else { panic!("expected Pi") };
    let Node::Pi(vih_dom_true, _) = vrest_true.node() else { panic!("expected Pi") };

    let value_case_false_expected = subst_top(&value_per_tag_d1, &false_val);
    let Node::Pi(vf_dom_false, vrest_false) = value_case_false_expected.node() else { panic!("expected Pi") };
    let Node::Pi(vih_dom_false, _) = vrest_false.node() else { panic!("expected Pi") };

    // Rebuild, under `case_*_val`'s own f/ih binders (depth 2), the
    // exact induction-hypothesis closure `whnf_in`'s own WRec-Sup
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
        let type_step_at_tag = app(shift(type_step, 0, 2), tag2);
        let target_ty = app(app(type_step_at_tag, f_ref), *rec_step);

        let c_at_tag = app(shift(type_motive_c, 0, 2), tag2);
        let eq_inst = app(app(app(shift(eq_ref, 0, 2), shift(type_motive_c, 0, 2)), shift(case_true_ty, 0, 2)), shift(case_false_ty, 0, 2));
        let f_cong = lam(c_at_tag, app(app(var(0), shift(&f_ref, 0, 1)), shift(rec_step, 0, 1)));
        let cong_step = cong1(&c_at_tag, &sort(0), &f_cong, type_step_at_tag, shift(case_ty, 0, 2), eq_inst);

        // `witness`/`witness_ty` are given at *ambient* (outer-test)
        // depth -- everything else here is already shifted for this
        // function's own depth-2 (f, ih) scope, so these need the same
        // +2 shift for `sym`/`transport` to compare like-for-like.
        let witness_ty2 = shift(witness_ty, 0, 2);
        let witness2 = shift(witness, 0, 2);
        let bridge = sym(&sort(0), &target_ty, &witness_ty2, cong_step);
        let _ = p;
        lam(*f_dom, lam(*ih_dom, transport(0, witness_ty2, target_ty, bridge, witness2)))
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
        &vf_dom_true,
        &vih_dom_true,
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
        &vf_dom_false,
        &vih_dom_false,
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
    let value_step = app(app(app(nat.bool_rec(&p), value_motive_c), case_true_val), case_false_val);
    p.check(&value_step, &value_expected_step_ty).expect("value_step : Pi b:Bool. value_motive_c(b)");

    // b_val := wrec(value_motive, ChildTy(Var0), value_step, a) --
    // standalone, at the SAME (ambient) depth as `a` itself, no extra
    // binder (unlike `fam`, this isn't going *inside* anything).
    let b_val = wrec(value_motive, wb, value_step, a);
    let expected_b_ty = subst_top(&fam, &a);
    p.check(&b_val, &expected_b_ty).expect("b_val : subst_top(fam, a) -- the core claim, isolated");

    // Sanity: `a` is genuinely symbolic, not secretly concrete -- whnf
    // doesn't reduce a bare postulate reference to `Sup(..)`, and
    // `fam(a)` doesn't secretly normalize to some closed Sort0 type
    // either (both would make this whole exercise vacuous).
    assert_eq!(whnf(&a), a, "the tag must stay an unreduced postulate reference, not secretly a concrete Sup");
    assert!(
        !matches!(nf(&expected_b_ty).node(), Node::Sort(_) | Node::W(..)),
        "fam(a) must stay stuck for symbolic a, not secretly collapse to a closed type: {:?}",
        nf(&expected_b_ty)
    );

    // --- THE ULTIMATE CLAIM: Pair(fam, a, b_val) typechecks as
    // Sigma(Nat, fam), for `a` a genuinely symbolic tag -- unlike the
    // earlier tagged-Sigma investigation (RELATED_WORK.md sec 14),
    // which needed `a` concrete before `Pair`'s own definitional-
    // equality check could ever succeed.
    let pr = pair(fam, a, b_val);
    let pr_ty = p.infer(&pr).expect("Pair(fam, a, b_val) should typecheck for a SYMBOLIC tag");
    assert!(def_eq(&pr_ty, &sigma_ty), "Pair's own inferred type should be Sigma(Nat, fam): got {pr_ty:?}");
}

