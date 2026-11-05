use super::*;

/// `shr1 A = shr1 B` (or `0 = shr1 B`, as `shr1 0`) for machine-expressible `A`, `B`, without a lookahead machine: the
/// bit-0 mask law `shr1 t = shr1 (t & M)`, `M = shl1 -1`, turns the pair into the shift-free law `A & M = B & M`
/// (search note section 47).
pub fn shr_mask_eq(job: &mut Job, n: usize, k: usize, a: &Term, b: &Term) -> Option<PlanRc> {
    let shr = |t: &Term| Term::op(SHR1, *t, Term::ZERO);
    let (mask, one_arg) = (Term::op(SHL1, Term::ONES, Term::ZERO), |t: &Term| match *t.node() {
        Node::Op(SHR1, x, _) if Machine::parse(&x).is_some() => Some(x),
        Node::Zero => Some(Term::ZERO),
        _ => None,
    });
    if job.setup().ablated("shrmask") || !matches!(*a.node(), Node::Op(SHR1, ..)) && !matches!(*b.node(), Node::Op(SHR1, ..)) {
        return None;
    }
    let (x, y) = (one_arg(a)?, one_arg(b)?);
    // the pair `A & M`, `B & M`: rewrite both, close with `prove_eq` (a machine law when they stay arithmetic)
    let (ta, tb) = (Term::op(AND, x, mask), Term::op(AND, y, mask));
    let ((r1, p1), (r2, p2)) = (rewrite(job, &ta, n, k), rewrite(job, &tb, n, k));
    let mid = prove_eq(job, n, k, &r1, &r2)?;
    let cong = Plan::cong(job, SHR1, Plan::trans(job, p1, Plan::trans(job, mid, Plan::sym(job, p2))), Plan::refl(job, &Term::ZERO));
    // `a = shr1 (A & M)` and `b = shr1 (B & M)`
    let mut side_proof = |orig: &Term, arg: &Term| -> Option<PlanRc> {
        if matches!(*orig.node(), Node::Zero) {
            // `0 = shr1 0 = shr1 (0 & M)`: the second step is a congruence on `0 = 0 & M` by the rewriter
            let (r, pr) = rewrite(job, &Term::op(AND, Term::ZERO, mask), n, k);
            if r != Term::ZERO {
                return None;
            }
            let (target, step) = rule_step(job, &shr(&Term::ZERO))?;
            if target != Term::ZERO {
                return None;
            }
            Some(Plan::trans(job, Plan::sym(job, step), Plan::cong(job, SHR1, Plan::sym(job, pr), Plan::refl(job, &Term::ZERO))))
        } else {
            Some(Plan::law(job, LawKind::Rule("shrmask"), shr(&Term::v(0)), shr(&Term::op(AND, Term::v(0), mask)), vec![*arg]))
        }
    };
    let (pa, pb) = (side_proof(a, &x)?, side_proof(b, &y)?);
    Some(Plan::trans(job, Plan::trans(job, pa, cong), Plan::sym(job, pb)))
}

/// The plan of `t1 = t2` over `k` variables: both sides rewritten, then closed with `prove_eq`; `None` when that cannot.
pub fn rewrite_plan(job: &mut Job, n: usize, k: usize, t1: &Term, t2: &Term) -> Option<PlanRc> {
    // an `lt` root (a one-bit result) is rewritten under its operands, then closed by congruence or, failing that,
    // by the `lt` machine proof for the rewritten pair; `lt` occurs only at the root
    let lt_roots = matches!((*t1.node(), *t2.node()), (Node::Op(LT, ..), Node::Op(LT, ..)));
    // each side gets the whole `RewriteState::budget`, so a side that cycles cannot leave the other half-normalized; afterwards the
    // budget is what the hungrier side left, so `job.rw.budget <= 0` still says some side used it up
    let budget0 = job.rw.budget;
    let ((r1, p1), left1) = (rewrite(job, t1, n, k), std::mem::replace(&mut job.rw.budget, budget0));
    let (r2, p2) = rewrite(job, t2, n, k);
    job.rw.budget = job.rw.budget.min(left1);
    let (p1, p2, mid) = if lt_roots {
        // `rewrite` normalizes the operands and applies the root rules; equal results close by `refl`, `lt` roots with
        // provable operands by congruence, the rest by the `lt` machine proof of the rewritten pair
        let mid = if r1 == r2 {
            Plan::refl(job, &r1)
        } else {
            let by_operands = if let (Node::Op(LT, a2, b2), Node::Op(LT, c2, d2)) = (*r1.node(), *r2.node()) {
                match (prove_eq(job, n, k, &a2, &c2), prove_eq(job, n, k, &b2, &d2)) {
                    (Some(pa), Some(pb)) => Some(Plan::cong(job, LT, pa, pb)),
                    _ => None,
                }
            } else {
                None
            };
            match by_operands {
                Some(plan) => plan,
                None => join_or_machine(job, n, k, &r1, &r2)?,
            }
        };
        (p1, p2, mid)
    } else {
        match prove_eq(job, n, k, &r1, &r2) {
            Some(mid) => (p1, p2, mid),
            // the rewriter may have pushed the shifts down to atoms; the mask reduction applies to the original sides
            None => (Plan::refl(job, t1), Plan::refl(job, t2), shr_mask_eq(job, n, k, t1, t2)?),
        }
    };
    Some(Plan::trans(job, Plan::trans(job, p1, mid), Plan::sym(job, p2)))
}

/// Proof of `t1 = t2` over `k` good vectors: `rewrite_plan`, compiled. `None` when there is no plan.
pub fn rewrite_law(job: &mut Job, n: usize, k: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    let plan = rewrite_plan(job, n, k, t1, t2)?;
    Some(law_proof(job, n, k, t1, t2, &plan))
}

/// The closed law `forall x.. gx... t1 = t2` proved by `plan`.
pub fn law_proof(job: &mut Job, n: usize, k: usize, t1: &Term, t2: &Term, plan: &Plan) -> (Expr, Expr) {
    let c = Compiler::new(n, k);
    let bv = bv_ty(n);
    let root = if matches!((*t1.node(), *t2.node()), (Node::Op(LT, ..), Node::Op(LT, ..))) { bv_ty(1) } else { bv };
    let (mut proof, mut stmt) = (c.proof(job, plan).2, id(root, c.ev(t1), c.ev(t2)));
    for _ in 0..k {
        let g = app(good_bv(n), var(k as u32 - 1));
        (proof, stmt) = (lam(g, proof), pi(g, stmt));
    }
    for _ in 0..k {
        (proof, stmt) = (lam(bv, proof), pi(bv, stmt));
    }
    (proof, stmt)
}

// ---- Carry-chain builder (search note section 13): `add A B = T` for bitwise A, B, T over x, y, with no
// lemma-specific template. It *discovers* the proof invariant: a constant value R for the carry that is
// inductive (the carry stays R for every pair of operand bits, starting from the initial `false`) and under
// which every sum bit equals the target bit. Both are decided by truth table before anything is built.

/// The constant carry value (as a literal bit) that works for `add a b = t`, if any.
pub fn find_constant_carry(a: &Term, b: &Term, t: &Term) -> Option<bool> {
    [false, true].into_iter().find(|&r| {
        // the initial carry is `false`, so only `false` can be maintained from the start
        !r && (0..4).all(|m| {
            let bits = [m & 1 == 1, m & 2 == 2];
            let [ab, bb, tb] = [a, b, t].map(|x| term_gb(&Bools, x, &bits));
            Bools.maj(&ab, &bb, &r) == r && Bools.sum3(&ab, &bb, &r) == tb
        })
    })
}

/// Proof of `t1 = t2` where `t1 = add A B` (bitwise `A`, `B`) and `t2` is bitwise, over two good vectors, by the
/// discovered constant-carry invariant; `None` when no constant carry works.
pub fn carry_chain_law(n: usize, t1: &Term, t2: &Term) -> Option<(Expr, Expr)> {
    let Node::Op(ADD, a_term, b_term) = *t1.node() else { return None };
    if a_term.uses_add() || b_term.uses_add() || t2.uses_add() || t1.max_var().max(t2.max_var()) > 1 {
        return None;
    }
    let r = bit(find_constant_carry(&a_term, &b_term, t2)?);
    let carry = |x: Expr, y: Expr, c: Expr| or(and(x, y), and(c, xor(x, y)));
    // per-bit lemmas, by case analysis on the two operand bits
    let (p_carry, _) = lemma2(
        &|x, y| id(bool0(), carry(a_term.bit(&[x, y]), b_term.bit(&[x, y]), r), r),
        &|_, _| refl(r),
    );
    let (p_sum, _) = lemma2(
        &|x, y| id(bool0(), sum3(a_term.bit(&[x, y]), b_term.bit(&[x, y]), r), t2.bit(&[x, y])),
        &|vx, vy| refl(t2.bit(&[bit(vx), bit(vy)])),
    );
    Some(two_var_law(n, t1, t2, &|a, ga, b, gb| {
        let bl = bool0();
        let (ai, bi) = (|i: usize| a_term.bit(&[a(i), b(i)]), |i: usize| b_term.bit(&[a(i), b(i)]));
        let mut c = vec![r];
        let mut pc: Vec<Option<Expr>> = vec![None];
        let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
        for i in 0..n {
            let args = vec![a(i), b(i), ga(i), gb(i)];
            // sum bit: rewrite the carry to R, then the sum lemma
            let s_i = sum3(ai(i), bi(i), c[i]);
            let to_target = apps(p_sum, args.clone());
            e.push(match &pc[i] {
                None => to_target,
                Some(pci) => {
                    let fmap = lam(bl, sum3(shift(&ai(i), 0, 1), shift(&bi(i), 0, 1), var(0)));
                    let rewritten = cong1(&bl, &bl, &fmap, c[i], r, *pci);
                    trans_proof(&bl, &s_i, &sum3(ai(i), bi(i), r), &t2.bit(&[a(i), b(i)]), rewritten, to_target)
                }
            });
            s1.push(s_i);
            s2.push(t2.bit(&[a(i), b(i)]));
            // next carry stays R
            let next = carry(ai(i), bi(i), c[i]);
            let stays = apps(p_carry, args);
            pc.push(Some(match &pc[i] {
                None => stays,
                Some(pci) => {
                    let fmap = lam(bl, carry(shift(&ai(i), 0, 1), shift(&bi(i), 0, 1), var(0)));
                    let rewritten = cong1(&bl, &bl, &fmap, c[i], r, *pci);
                    trans_proof(&bl, &next, &carry(ai(i), bi(i), r), &r, rewritten, stays)
                }
            }));
            c.push(next);
        }
        (s1, s2, e)
    }))
}

