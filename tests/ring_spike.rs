// Throwaway spike (docs/superpowers/specs/2026-10-10-ring-theory-prototype-spec.md): a postulated commutative-ring
// fragment and a kernel-checked proof of (a+b)(a+b) = (a*a + a*b) + (b*a + b*b) by explicit axiom applications.
use tatic::kernel::*;

#[test]
fn ring_square_expansion_checks() {
    let mut p = Postulates::new();
    let r = p.push(sort(0));
    let rt = p.get(r);
    let bin = p.push(arrow(rt.clone(), arrow(rt.clone(), rt.clone())));
    let (plus, times) = (p.get(bin), {
        let t = p.push(arrow(rt.clone(), arrow(rt.clone(), rt.clone())));
        p.get(t)
    });
    let a = { let c = p.push(rt.clone()); p.get(c) };
    let b = { let c = p.push(rt.clone()); p.get(c) };
    let pl = |x: Expr, y: Expr| app2(plus.clone(), x, y);
    let tm = |x: Expr, y: Expr| app2(times.clone(), x, y);
    let eq = |x: Expr, y: Expr| id(rt.clone(), x, y);
    // distrib_l: Pi x y z. x*(y+z) = x*y + x*z (context [x, y, z]: x = var 2, y = var 1, z = var 0)
    let (x, y, z) = (var(2), var(1), var(0));
    let dl_ty = pi(rt.clone(), pi(rt.clone(), pi(rt.clone(), eq(tm(x.clone(), pl(y.clone(), z.clone())), pl(tm(x.clone(), y.clone()), tm(x.clone(), z.clone()))))));
    let dl = { let c = p.push(dl_ty); p.get(c) };
    // distrib_r: Pi x y z. (x+y)*z = x*z + y*z
    let dr_ty = pi(rt.clone(), pi(rt.clone(), pi(rt.clone(), eq(tm(pl(x.clone(), y.clone()), z.clone()), pl(tm(x.clone(), z.clone()), tm(y.clone(), z.clone()))))));
    let dr = { let c = p.push(dr_ty); p.get(c) };

    let s = pl(a.clone(), b.clone());
    let lhs = tm(s.clone(), s.clone());
    let mid = pl(tm(a.clone(), s.clone()), tm(b.clone(), s.clone()));
    let rhs = pl(pl(tm(a.clone(), a.clone()), tm(a.clone(), b.clone())), pl(tm(b.clone(), a.clone()), tm(b.clone(), b.clone())));
    // (a+b)(a+b) = a(a+b) + b(a+b)
    let p1 = apps3(&dr, &a, &b, &s);
    // a(a+b) = aa + ab ; b(a+b) = ba + bb
    let d1 = apps3(&dl, &a, &a, &b);
    let d2 = apps3(&dl, &b, &a, &b);
    let (l1, r1) = (tm(a.clone(), s.clone()), pl(tm(a.clone(), a.clone()), tm(a.clone(), b.clone())));
    let (l2, r2) = (tm(b.clone(), s.clone()), pl(tm(b.clone(), a.clone()), tm(b.clone(), b.clone())));
    let p2 = cong_n(&rt, &rt, &plus, &[l1, l2], &[r1, r2], vec![d1, d2]);
    let proof = trans_proof(&rt, &lhs, &mid, &rhs, p1, p2);
    p.check(&proof, &eq(lhs.clone(), rhs.clone())).expect("kernel accepts the expansion");
    // a wrong target is rejected
    let wrong = eq(lhs, pl(tm(a.clone(), a.clone()), tm(b.clone(), b.clone())));
    assert!(p.check(&proof, &wrong).is_err());
}

fn apps3(f: &Expr, x: &Expr, y: &Expr, z: &Expr) -> Expr {
    app(app2(f.clone(), x.clone(), y.clone()), z.clone())
}
