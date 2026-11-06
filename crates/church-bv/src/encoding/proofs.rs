use super::*;

/// `(proof, statement)` of `Pi x:Bv_n. GoodBv x -> Id(Bv_n, add x (lit rhs_lit), x)` using the
/// `add x 0 = x` proof; `rhs_lit != 0` gives a statement the proof must not check against.
pub fn add_zero_proof(n: usize, rhs_lit: u128) -> (Expr, Expr) {
    add_identity_proof(n, rhs_lit, false)
}

/// `left = true` proves `add zero x = x` instead (the literal is the first operand).
pub fn add_identity_proof(n: usize, rhs_lit: u128, left: bool) -> (Expr, Expr) {
    add_identity_proof_over(n, rhs_lit, left, add)
}

/// Same, with the statement stated over `adder` (`add` or `add_shared`); the proof body is unchanged,
/// so `adder`'s result must be convertible to the inlined-carry tuple the proof builds.
pub fn add_identity_proof_over(n: usize, rhs_lit: u128, left: bool, adder: fn(usize) -> Expr) -> (Expr, Expr) {
    // `xor(a, false)` with the operands in the order `add` uses them
    let xf = move |a: Expr| if left { xor(f(), a) } else { xor(a, f()) };
    let carry = move |a: Expr, c: Expr| {
        if left { or(and(f(), a), and(c, xor(f(), a))) } else { or(and(a, f()), and(c, xor(a, f()))) }
    };
    let (p1, _) = bit_lemma(id(bool0(), xor(xf(var(0)), f()), var(0)), refl(t()), refl(f()));
    let (p2, _) = bit_lemma(id(bool0(), carry(var(0), f()), f()), refl(f()), refl(f()));

    // ctx of the step body: [x, g, a_0..a_(n-1), ga_0..ga_(n-1)], depth d = 2 + 2n
    let d = 2 + 2 * n;
    let a = |i: usize| var((d - 1 - (2 + i)) as u32);
    let ga = |i: usize| var((d - 1 - (2 + n + i)) as u32);
    // carries c_0 = false, c_(i+1) = carry(a_i, c_i), with proofs pc_i : Id(c_i, false)
    let mut c = vec![f()];
    let mut pc: Vec<Option<Expr>> = vec![None]; // None = c_0 is literally `false`
    for i in 0..n {
        let next = carry(a(i), c[i]);
        // carry(a_i, c_i) = carry(a_i, false) by c_i = false, then = false by the bit lemma
        let step_to_false = app2(p2, a(i), ga(i));
        let proof = match &pc[i] {
            None => step_to_false,
            Some(pci) => {
                let ai1 = shift(&a(i), 0, 1);
                let fmap = lam(bool0(), carry(ai1, var(0)));
                let rewritten = cong1(&bool0(), &bool0(), &fmap, c[i], f(), *pci);
                trans_proof(&bool0(), &next, &carry(a(i), f()), &f(), rewritten, step_to_false)
            }
        };
        c.push(next);
        pc.push(Some(proof));
    }
    // sum bits s_i = xor(xor(a_i, false), c_i) = a_i
    let mut s = Vec::new();
    let mut e = Vec::new();
    for i in 0..n {
        let s_i = xor(xf(a(i)), c[i]);
        let to_a = app2(p1, a(i), ga(i)); // xor(xf(a_i),f) = a_i
        let proof = match &pc[i] {
            None => to_a,
            Some(pci) => {
                let ai1 = shift(&a(i), 0, 1);
                let fmap = lam(bool0(), xor(xf(ai1), var(0)));
                let rewritten = cong1(&bool0(), &bool0(), &fmap, c[i], f(), *pci);
                trans_proof(&bool0(), &s_i, &xor(xf(a(i)), f()), &a(i), rewritten, to_a)
            }
        };
        s.push(s_i);
        e.push(proof);
    }
    let ys: Vec<Expr> = (0..n).map(a).collect();
    // f_n = \u_0..u_(n-1). \C k. k u_0 .. u_(n-1)   (ctx [u.., C, k]: k = var0, u_i = var(n+1-i))
    let fbody = bits_to_bv(n);
    let body = cong_n(&bool0(), &bv_ty(n), &fbody, &s, &ys, e);
    let mut step = body;
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    let rhs = lit(n, rhs_lit);
    let sum = |x: Expr, r: Expr| if left { app2(adder(n), r, x) } else { app2(adder(n), x, r) };
    let motive = lam(bv_ty(n), id(bv_ty(n), sum(var(0), rhs), var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), id(bv_ty(n), sum(var(0), rhs), var(0))));
    (proof, stmt)
}

/// `add_identity_proof_over` with the carries bound once in the proof as well (design doc section 90b): each carry `c_j`
/// and its proof `pc_j : Id(c_j, false)` are lambda-bound variables, `(\c pc. rest) (carry a_(j-1) c_(j-1)) proof_j`, so
/// every term and type the proof body builds mentions `c_j` as one variable, not an O(j)-node expression. Stated over
/// `adder` (use `add_shared`, so the statement is shaped the same way).
pub fn add_identity_proof_shared(n: usize, rhs_lit: u128, left: bool, adder: fn(usize) -> Expr) -> (Expr, Expr) {
    let xf = move |a: Expr| if left { xor(f(), a) } else { xor(a, f()) };
    let carry = move |a: Expr, c: Expr| {
        if left { or(and(f(), a), and(c, xor(f(), a))) } else { or(and(a, f()), and(c, xor(a, f()))) }
    };
    let (p1, _) = bit_lemma(id(bool0(), xor(xf(var(0)), f()), var(0)), refl(t()), refl(f()));
    let (p2, _) = bit_lemma(id(bool0(), carry(var(0), f()), f()), refl(f()), refl(f()));
    // step-body context [x, g, a_0..a_(n-1), ga_0..ga_(n-1), c_1, pc_1, c_2, pc_2, ..]; `k` pairs are bound
    let d = 2 + 2 * n;
    let a = move |i: usize, k: usize| var((d + 2 * k - 1 - (2 + i)) as u32);
    let ga = move |i: usize, k: usize| var((d + 2 * k - 1 - (2 + n + i)) as u32);
    let cv = move |j: usize, k: usize| if j == 0 { f() } else { var((d + 2 * k - 1 - (d + 2 * (j - 1))) as u32) };
    let pv = move |j: usize, k: usize| var((d + 2 * k - 1 - (d + 2 * (j - 1) + 1)) as u32);
    // proof that c_(j+1) = carry(a_j, c_j) is false, at `k` bound pairs (j <= k)
    let next_false = |j: usize, k: usize| {
        let step_to_false = app2(p2, a(j, k), ga(j, k));
        if j == 0 {
            return step_to_false;
        }
        let cj = cv(j, k);
        let fmap = lam(bool0(), carry(shift(&a(j, k), 0, 1), var(0)));
        let rewritten = cong1(&bool0(), &bool0(), &fmap, cj, f(), pv(j, k));
        trans_proof(&bool0(), &carry(a(j, k), cj), &carry(a(j, k), f()), &f(), rewritten, step_to_false)
    };
    let kn = n.saturating_sub(1);
    // innermost: the sums with every carry a variable
    let mut s = Vec::new();
    let mut e = Vec::new();
    for i in 0..n {
        let ci = cv(i, kn);
        let s_i = xor(xf(a(i, kn)), ci);
        let to_a = app2(p1, a(i, kn), ga(i, kn));
        let proof = if i == 0 {
            to_a
        } else {
            let fmap = lam(bool0(), xor(xf(shift(&a(i, kn), 0, 1)), var(0)));
            let rewritten = cong1(&bool0(), &bool0(), &fmap, ci, f(), pv(i, kn));
            trans_proof(&bool0(), &s_i, &xor(xf(a(i, kn)), f()), &a(i, kn), rewritten, to_a)
        };
        s.push(s_i);
        e.push(proof);
    }
    let ys: Vec<Expr> = (0..n).map(|i| a(i, kn)).collect();
    let fbody = bits_to_bv(n);
    let mut body = cong_n(&bool0(), &bv_ty(n), &fbody, &s, &ys, e);
    // bind c_(j+1), pc_(j+1) from the inside out: level k binds the pair for j = k
    for k in (0..kn).rev() {
        let binder = lam(bool0(), lam(id(bool0(), var(0), f()), body));
        body = app2(binder, carry(a(k, k), cv(k, k)), next_false(k, k));
    }
    let mut step = body;
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    let rhs = lit(n, rhs_lit);
    let sum = |x: Expr, r: Expr| if left { app2(adder(n), r, x) } else { app2(adder(n), x, r) };
    let motive = lam(bv_ty(n), id(bv_ty(n), sum(var(0), rhs), var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), id(bv_ty(n), sum(var(0), rhs), var(0))));
    (proof, stmt)
}

// ---- Commutativity: `add x y = add y x` for `x`, `y` with `GoodBv` witnesses.

/// Closed proof of `Pi a b c c'. GoodBool a -> GoodBool b -> Id(c, c') -> Id(F(a,b,c), F(b,a,c'))`,
/// by case analysis on `a` and `b` only (`c`, `c'` stay symbolic). Each leaf is a congruence in
/// the last argument; the swap `F(a,b,_)` vs `F(b,a,_)` is closed by conversion once `a`, `b` are
/// literal bits (it is valid only for an `F` that is commutative in its first two arguments).
pub fn comm_lemma(ff: &dyn Fn(Expr, Expr, Expr) -> Expr) -> Expr {
    // ctx [a, b, c, c', ga, gb]
    fn elim(ff: &dyn Fn(Expr, Expr, Expr) -> Expr, vals: [Option<bool>; 2]) -> Expr {
        let which = match vals.iter().position(|v| v.is_none()) {
            Some(w) => w,
            None => {
                let (av, bv) = (bit(vals[0].unwrap()), bit(vals[1].unwrap()));
                let fmap = lam(bool0(), ff(av, bv, var(0)));
                // under the \p binder: c = var 4, c' = var 3
                return lam(id(bool0(), var(3), var(2)), cong1(&bool0(), &bool0(), &fmap, var(4), var(3), var(0)));
            }
        };
        // motive at depth 7 (inside its own binder): c = var 4, c' = var 3
        let operand = |k: usize| match vals[k] {
            _ if k == which => var(0),
            Some(v) => bit(v),
            None => var(6 - k as u32),
        };
        let (x, y) = (operand(0), operand(1));
        let body = pi(
            id(bool0(), var(4), var(3)),
            id(
                bool0(),
                shift(&ff(x, y, var(4)), 0, 1),
                shift(&ff(y, x, var(3)), 0, 1),
            ),
        );
        let motive = lam(bool0(), body);
        let g = var(1 - which as u32);
        let mut vt = vals;
        vt[which] = Some(true);
        let mut vf = vals;
        vf[which] = Some(false);
        app3(g, motive, elim(ff, vt), elim(ff, vf))
    }
    let body = elim(ff, [None, None]);
    lam(bool0(), lam(bool0(), lam(bool0(), lam(bool0(),
        lam(app(good_bool(), var(3)), lam(app(good_bool(), var(3)), body))))))
}

/// `(proof, statement)` of `Pi x y. GoodBv x -> GoodBv y -> Id(Bv_n, add x y, add y x)`.
/// `wrong` changes the statement's right-hand side to `add x x`, which the proof must not check against.
pub fn add_comm_proof(n: usize, wrong: bool) -> (Expr, Expr) {
    let carry = |a: Expr, b: Expr, c: Expr| or(and(a, b), and(c, xor(a, b)));
    let sum = |a: Expr, b: Expr, c: Expr| xor(xor(a, b), c);
    let cc = comm_lemma(&carry);
    let sc = comm_lemma(&sum);
    // ctx: x, y, gx, gy, a_0.., ga_0.., b_0.., gb_0..
    let d1 = 4 + 2 * n;
    let d2 = d1 + 2 * n;
    let a = |i: usize| var((d2 - 1 - (4 + i)) as u32);
    let ga = |i: usize| var((d2 - 1 - (4 + n + i)) as u32);
    let b = |i: usize| var((d2 - 1 - (d1 + i)) as u32);
    let gb = |i: usize| var((d2 - 1 - (d1 + n + i)) as u32);
    // c_i = carry of add (mk a) (mk b); c'_i = carry of add (mk b) (mk a); pc_i : Id(c_i, c'_i)
    let mut c = vec![f()];
    let mut c2 = vec![f()];
    let mut pc = vec![refl(f())];
    let (mut s, mut s2, mut e) = (vec![], vec![], vec![]);
    for i in 0..n {
        s.push(sum(a(i), b(i), c[i]));
        s2.push(sum(b(i), a(i), c2[i]));
        e.push(apps(sc, vec![a(i), b(i), c[i], c2[i], ga(i), gb(i), pc[i]]));
        let (nc, nc2) = (carry(a(i), b(i), c[i]), carry(b(i), a(i), c2[i]));
        pc.push(apps(cc, vec![a(i), b(i), c[i], c2[i], ga(i), gb(i), pc[i]]));
        c.push(nc);
        c2.push(nc2);
    }
    // f_n = \u_0..u_(n-1). \C k. k u_0 .. u_(n-1)
    let fbody = bits_to_bv(n);
    let step_y = binders(n, cong_n(&bool0(), &bv_ty(n), &fbody, &s, &s2, e));
    // inside the a-step (depth d1): eliminate y
    let a1 = |i: usize| var((d1 - 1 - (4 + i)) as u32);
    let mka = church_tuple(&(0..n).map(|i| shift(&a1(i), 0, 1)).collect::<Vec<_>>());
    let motive_y = lam(bv_ty(n), id(bv_ty(n), app2(add(n), mka, var(0)), app2(add(n), var(0), mka)));
    let gy = var((d1 - 1 - 3) as u32);
    let step_x = binders(n, app2(gy, motive_y, step_y));
    let rhs = |x: Expr, y: Expr| if wrong { app2(add(n), x, x) } else { app2(add(n), y, x) };
    // depth 5 (inside the motive binder): x' = var 0, y = var 3
    let motive_x = lam(bv_ty(n), id(bv_ty(n), app2(add(n), var(0), var(3)), rhs(var(0), var(3))));
    let body = app2(var(1), motive_x, step_x);
    let proof = lam(bv_ty(n), lam(bv_ty(n), lam(app(good_bv(n), var(1)), lam(app(good_bv(n), var(1)), body))));
    // statement at ctx [x, y, gx, gy]: x = var 3, y = var 2
    let stmt = pi(bv_ty(n), pi(bv_ty(n), pi(app(good_bv(n), var(1)), pi(app(good_bv(n), var(1)),
        id(bv_ty(n), app2(add(n), var(3), var(2)), rhs(var(3), var(2)))))));
    (proof, stmt)
}

// ---- H4 (design doc section 89): `toN (or a b) = toN a + toN b` when the bit ranges are disjoint.

/// `\a b. \C k. a C (\a_i.. b C (\b_i.. k (op a_0 b_0) .. (op a_(n-1) b_(n-1))))`, like `add` with no carry.
pub fn bitwise(n: usize, op: &dyn Fn(Expr, Expr) -> Expr) -> Expr {
    let d = 4 + 2 * n;
    let v = |pos: usize| var((d - 1 - pos) as u32);
    let outs = (0..n).map(|i| op(v(4 + i), v(4 + n + i))).collect();
    let mut body = apps(v(3), outs);
    for _ in 0..n {
        body = lam(bool0(), body);
    }
    let mut inner = app2(var(n as u32 + 2), var(n as u32 + 1), body);
    for _ in 0..n {
        inner = lam(bool0(), inner);
    }
    lam(bv_ty(n), lam(bv_ty(n), lam(sort(1), lam(karrow(n), app2(var(3), var(1), inner)))))
}
pub fn or_bv(n: usize) -> Expr {
    bitwise(n, &|a, b| or(a, b))
}
pub fn good_or_bv(n: usize) -> (Expr, Expr) {
    let (g_or, _) = good2(&|a, b| or(a, b), &OP_INFO[2].truth);
    good_vec(n, or_bv(n), &move |a, b, ga, gb| {
        let s = (0..n).map(|i| or(a[i], b[i])).collect();
        let gs = (0..n).map(|i| apps(g_or, vec![a[i], b[i], ga[i], gb[i]])).collect();
        (s, gs)
    })
}
/// `\P st. st bits.. goods..`: the canonical `GoodBv (mk bits)` from `GoodBool` witnesses.
pub fn good_tuple(bits: &[Expr], goods: &[Expr]) -> Expr {
    let n = bits.len();
    let sh = |e: &Expr| shift(e, 0, 2);
    lam(arrow(bv_ty(n), sort(2)), lam(good_bv_step(n), apps(var(0), bits.iter().chain(goods).map(sh).collect())))
}

/// `(proof, statement)`: for `a` with free low bits `0..k` (higher bits false) and `b` with free high bits
/// `k..n` (lower bits false), `toN (or a b) = toN a + toN b`, each with its canonical witness.
pub fn or_disjoint_proof(n: usize, k: usize, stated_sum_with_a_twice: bool) -> (Expr, Expr) {
    let (g_or_bv, _) = good_or_bv(n);
    // ctx [bit_0..bit_(n-1), g_0..g_(n-1)]
    let d = 2 * n;
    let bit_v = |j: usize| var((d - 1 - j) as u32);
    let good_v = |j: usize| var((d - 1 - (n + j)) as u32);
    let a_bits: Vec<Expr> = (0..n).map(|i| if i < k { bit_v(i) } else { f() }).collect();
    let a_good: Vec<Expr> = (0..n).map(|i| if i < k { good_v(i) } else { good_bit(false) }).collect();
    let b_bits: Vec<Expr> = (0..n).map(|i| if i >= k { bit_v(i) } else { f() }).collect();
    let b_good: Vec<Expr> = (0..n).map(|i| if i >= k { good_v(i) } else { good_bit(false) }).collect();
    // `mk` shifts its arguments by 2; `good_tuple` does too, so both take the operands at depth d
    let (x, y) = (church_tuple(&a_bits), church_tuple(&b_bits));
    let (gx, gy) = (good_tuple(&a_bits, &a_good), good_tuple(&b_bits, &b_good));
    let gor = apps(g_or_bv, vec![x, y, gx, gy]);
    let lhs = app2(to_n(n), app2(or_bv(n), x, y), gor);
    let (tx, ty) = (app2(to_n(n), x, gx), app2(to_n(n), y, gy));
    let rhs = if stated_sum_with_a_twice { app2(nat_add(), tx, tx) } else { app2(nat_add(), tx, ty) };
    let mut proof = refl(lhs);
    let mut stmt = id(nat_ty(), lhs, rhs);
    for _ in 0..n {
        proof = lam(app(good_bool(), var(n as u32 - 1)), proof);
        stmt = pi(app(good_bool(), var(n as u32 - 1)), stmt);
    }
    for _ in 0..n {
        proof = lam(bool0(), proof);
        stmt = pi(bool0(), stmt);
    }
    (proof, stmt)
}

// ---- Associativity of `add` (search note section 11). The two sides keep separate carry states, (c, d) for
// `add (add x y) z` and (e, f) for `add x (add y z)`. Only the *total* matters: c + d = e + f, encoded as the
// pair (xor c d, and c d). Each side's output bit and next pair is a fixed function of (a, b, z, xor, and)
// (a 5-variable case analysis with `refl` leaves, no hypotheses), so the two sides agree by `cong_n` on the
// two equalities carried from the previous bit.

/// `(proof, statement)` of `Pi x y z. GoodBv x -> GoodBv y -> GoodBv z -> Id(Bv_n, add (add x y) z, add x (add y z))`.
/// `wrong` states `add x (add y y)` on the right instead, which the proof must not check against.
pub fn add_assoc_proof(n: usize, wrong: bool) -> (Expr, Expr) {
    // six lemmas, by (left, which) over [a, b, z, c, d]: Id(F(c, d), G_which(a, b, z, xor c d, and c d))
    let lemma = |left: bool, which: usize| {
        lemma_n(
            5,
            &move |v| {
                let p = xor(v[3], v[4]);
                let q = and(v[3], v[4]);
                id(bool0(), assoc_side(left, which, v), assoc_g(which, &[v[0], v[1], v[2], p, q]))
            },
            &move |bits| refl(assoc_side(left, which, &bits.iter().map(|b| bit(*b)).collect::<Vec<_>>())),
        )
        .0
    };
    let lem: Vec<Vec<Expr>> = [true, false].iter().map(|&l| (0..3).map(|w| lemma(l, w)).collect()).collect();
    let gops = GoodOps::new();
    // ctx: x y z gx gy gz | a.. ga.. | b.. gb.. | z.. gz..
    let d1 = 6 + 2 * n;
    let d2 = 6 + 4 * n;
    let d3 = 6 + 6 * n;
    let at = |d: usize, pos: usize| var((d - 1 - pos) as u32);
    let a = |i: usize| at(d3, 6 + i);
    let ga = |i: usize| at(d3, 6 + n + i);
    let b = |i: usize| at(d3, 6 + 2 * n + i);
    let gb = |i: usize| at(d3, 6 + 3 * n + i);
    let z = |i: usize| at(d3, 6 + 4 * n + i);
    let gz = |i: usize| at(d3, 6 + 5 * n + i);
    let bl = bool0();
    let tr = |x: &Expr, y: &Expr, w: &Expr, p: Expr, q: Expr| trans_proof(&bl, x, y, w, p, q);
    let false_gb = Gb { e: f(), g: good_bit(false) };
    let (mut cl, mut dl, mut er, mut fr) = (false_gb.clone(), false_gb.clone(), false_gb.clone(), false_gb);
    let mut ip = refl(xor(f(), f()));
    let mut iq = refl(and(f(), f()));
    let (mut s1, mut s2, mut e) = (vec![], vec![], vec![]);
    for i in 0..n {
        let (ab, bb, zb) = (Gb { e: a(i), g: ga(i) }, Gb { e: b(i), g: gb(i) }, Gb { e: z(i), g: gz(i) });
        let (pl, ql) = (xor(cl.e, dl.e), and(cl.e, dl.e));
        let (pr, qr) = (xor(er.e, fr.e), and(er.e, fr.e));
        let abz = [a(i), b(i), z(i)];
        let inst = |left: bool, which: usize, c: &Gb, d: &Gb| {
            apps(lem[if left { 0 } else { 1 }][which], vec![
                a(i), b(i), z(i), c.e, d.e, ga(i), gb(i), gz(i), c.g, d.g,
            ])
        };
        let g_at = |which: usize, p: Expr, q: Expr| assoc_g(which, &[abz[0], abz[1], abz[2], p, q]);
        // Id(G(left state), G(right state)) from the two carried equalities
        let link = |which: usize, ip: &Expr, iq: &Expr| {
            let fmap = lam(bl, lam(bl, assoc_g(which, &[shift(&abz[0], 0, 2), shift(&abz[1], 0, 2), shift(&abz[2], 0, 2), var(1), var(0)])));
            cong_n(&bl, &bl, &fmap, &[pl, ql], &[pr, qr], vec![*ip, *iq])
        };
        // (F_left, F_right, proof of Id(F_left, F_right)) for `which`
        let eq = |which: usize| {
            let fl = assoc_side(true, which, &[abz[0], abz[1], abz[2], cl.e, dl.e]);
            let frr = assoc_side(false, which, &[abz[0], abz[1], abz[2], er.e, fr.e]);
            let (gl, gr) = (g_at(which, pl, ql), g_at(which, pr, qr));
            let right_back = sym(&bl, &frr, &gr, inst(false, which, &er, &fr));
            let mid = tr(&gl, &gr, &frr, link(which, &ip, &iq), right_back);
            let proof = tr(&fl, &gl, &frr, inst(true, which, &cl, &dl), mid);
            (fl, frr, proof)
        };
        let (fl0, fr0, p_out) = eq(0);
        let (_, _, p_p) = eq(1);
        let (_, _, p_q) = eq(2);
        s1.push(fl0);
        s2.push(fr0);
        e.push(p_out);
        ip = p_p;
        iq = p_q;
        let s = gops.sum3(&ab, &bb, &cl);
        let (ncl, ndl) = (gops.maj(&ab, &bb, &cl), gops.maj(&s, &zb, &dl));
        let t = gops.sum3(&bb, &zb, &er);
        let (ner, nfr) = (gops.maj(&bb, &zb, &er), gops.maj(&ab, &t, &fr));
        cl = ncl;
        dl = ndl;
        er = ner;
        fr = nfr;
    }
    let fbody = bits_to_bv(n);
    let step_z = binders(n, cong_n(&bool0(), &bv_ty(n), &fbody, &s1, &s2, e));
    let ad = add(n);
    let claim = |x: Expr, y: Expr, zz: Expr| {
        let rhs_z = if wrong { y } else { zz };
        id(bv_ty(n), app2(ad, app2(ad, x, y), zz), app2(ad, x, app2(ad, y, rhs_z)))
    };
    let mk_at = |d: usize, first: usize, extra: i32| church_tuple(&(0..n).map(|i| shift(&at(d, first + i), 0, extra)).collect::<Vec<_>>());
    // at depth d2: eliminate gz into a motive over z'
    let motive_z = lam(bv_ty(n), claim(mk_at(d2, 6, 1), mk_at(d2, 6 + 2 * n, 1), var(0)));
    let step_y = binders(n, app2(at(d2, 5), motive_z, step_z));
    // at depth d1: eliminate gy into a motive over y'
    let motive_y = lam(bv_ty(n), claim(mk_at(d1, 6, 1), var(0), shift(&at(d1, 2), 0, 1)));
    let step_x = binders(n, app2(at(d1, 4), motive_y, step_y));
    let motive_x = lam(bv_ty(n), claim(var(0), var(5), var(4)));
    let body = app2(var(2), motive_x, step_x);
    let g = |v: u32| app(good_bv(n), var(v));
    let proof = lam(bv_ty(n), lam(bv_ty(n), lam(bv_ty(n), lam(g(2), lam(g(2), lam(g(2), body))))));
    let stmt = pi(bv_ty(n), pi(bv_ty(n), pi(bv_ty(n), pi(g(2), pi(g(2), pi(g(2), claim(var(5), var(4), var(3))))))));
    (proof, stmt)
}

// ---- `add x (xor x -1) = -1` (x + ~x), a carry that stays false (search note section 12). The rewriter no longer uses it.

/// `(proof, statement)` of `Pi x. GoodBv x -> Id(Bv_n, add x (xor x -1), -1)`; `wrong` states `= 0` instead.
pub fn add_not_proof(n: usize, wrong: bool) -> (Expr, Expr) {
    let nb = |a: Expr| xor(a, t());
    let carry = move |a: Expr, c: Expr| or(and(a, nb(a)), and(c, xor(a, nb(a))));
    let sum = move |a: Expr, c: Expr| xor(xor(a, nb(a)), c);
    let (p1, _) = bit_lemma(id(bool0(), sum(var(0), f()), t()), refl(t()), refl(t()));
    let (p2, _) = bit_lemma(id(bool0(), carry(var(0), f()), f()), refl(f()), refl(f()));
    // ctx of the step body: [x, g, a_0..a_(n-1), ga_0..ga_(n-1)]
    let d = 2 + 2 * n;
    let a = |i: usize| var((d - 1 - (2 + i)) as u32);
    let ga = |i: usize| var((d - 1 - (2 + n + i)) as u32);
    let mut c = vec![f()];
    let mut pc: Vec<Option<Expr>> = vec![None];
    for i in 0..n {
        let next = carry(a(i), c[i]);
        let to_false = app2(p2, a(i), ga(i));
        let proof = match &pc[i] {
            None => to_false,
            Some(pci) => {
                let fmap = lam(bool0(), carry(shift(&a(i), 0, 1), var(0)));
                let rewritten = cong1(&bool0(), &bool0(), &fmap, c[i], f(), *pci);
                trans_proof(&bool0(), &next, &carry(a(i), f()), &f(), rewritten, to_false)
            }
        };
        c.push(next);
        pc.push(Some(proof));
    }
    let (mut s, mut e) = (vec![], vec![]);
    for i in 0..n {
        let s_i = sum(a(i), c[i]);
        let to_t = app2(p1, a(i), ga(i));
        let proof = match &pc[i] {
            None => to_t,
            Some(pci) => {
                let fmap = lam(bool0(), sum(shift(&a(i), 0, 1), var(0)));
                let rewritten = cong1(&bool0(), &bool0(), &fmap, c[i], f(), *pci);
                trans_proof(&bool0(), &s_i, &sum(a(i), f()), &t(), rewritten, to_t)
            }
        };
        s.push(s_i);
        e.push(proof);
    }
    let ys: Vec<Expr> = (0..n).map(|_| t()).collect();
    let fbody = bits_to_bv(n);
    let mut step = cong_n(&bool0(), &bv_ty(n), &fbody, &s, &ys, e);
    for _ in 0..n {
        step = lam(app(good_bool(), var(n as u32 - 1)), step);
    }
    for _ in 0..n {
        step = lam(bool0(), step);
    }
    let ones = lit(n, low_bits(n));
    let rhs = if wrong { lit(n, 0) } else { ones };
    let xv = bitwise(n, &|p, q| xor(p, q));
    let claim = |x: Expr| id(bv_ty(n), app2(add(n), x, app2(xv, x, ones)), rhs);
    let motive = lam(bv_ty(n), claim(var(0)));
    let proof = lam(bv_ty(n), lam(app(good_bv(n), var(0)), app2(var(0), motive, step)));
    let stmt = pi(bv_ty(n), arrow(app(good_bv(n), var(0)), claim(var(0))));
    (proof, stmt)
}

