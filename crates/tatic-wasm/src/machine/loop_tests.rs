//! The loop form's machine parts: `local.set` (the `Set` class) writes one parameter slot of the frame, and `Br`
//! restarts the function on the current frame.
use super::tests::{konst, row};
use super::*;

/// The test's `MeaningEnv` at the answer type `r` with the guard's else answer `z`: no `choose`, the environment of no functions (a call answers 0 at
/// the memory it was given), and `restart` as given.
fn meaning_env(c: &mut Cx, w: &Machine, r: At, z: At, restart: At) -> MeaningEnv {
    let n = w.n;
    let none = c.lam(w.v(), |c, _j| {
        c.lam(w.fr(), |c, _fr| {
            let mem = w.mem(c, r);
            c.lam(mem, |c, mu| {
                let ret = arrow(w.v(), arrow(w.mem(c, r), c.at(r)));
                c.lam(ret, |c, k| app2(c.at(k), lit(n, 0), c.at(mu)))
            })
        })
    });
    let none = c.mark(none);
    MeaningEnv { r, ch: None, z, calls: none, restart }
}

/// A `restart` for tests whose code holds no `Br`, or whose `Br` is not taken: `\fr mu. kk fr (0, s) mu` (`R` is
/// abstract, so no closed term fits).
fn restart_via(c: &mut Cx, w: &Machine, r: At, s_ty: At, kk: At, s: At) -> At {
    let n = w.n;
    let restart = c.lam(w.fr(), |c, fr2| {
        let mem = w.mem(c, r);
        c.lam(mem, |c, mu2| app3(c.at(kk), c.at(fr2), mkpair(c.at(s_ty), lit(n, 0), c.at(s)), c.at(mu2)))
    });
    c.mark(restart)
}

fn get(i: i64) -> Ins {
    Ins::Row { name: "local.get", operand: i }
}
fn set(i: i64) -> Ins {
    Ins::Row { name: "local.set", operand: i }
}

/// The width-3 frame `(s[0], (s[1], (s[2], s[3])))` of bound variables: a clobbered slot or terminal word shows, where
/// `Machine::frame`'s literal zeros would hide it. `word(i)` overrides slot `i`.
fn var_frame(c: &Cx, w: &Machine, s: [At; 4], word: &dyn Fn(usize) -> Option<Expr>) -> Expr {
    (0..3).rev().fold(c.at(s[3]), |acc, i| mkpair(w.words(2 - i, w.v()), word(i).unwrap_or_else(|| c.at(s[i])), acc))
}

/// Over a hand-built frame of variables, `[get 1, konst 1, add, Set i, get j]` hands the continuation the frame with
/// slot `i` replaced by `a1 + 1`, and pushes that word when `i == j` and slot `j`'s variable otherwise. Reading the old
/// slot after a write is rejected.
#[test]
fn local_set_writes_one_slot() {
    let t = crate::wasm::table();
    let w = Machine { n: 8, fw: 3, table: t };
    let n = w.n;
    // S R k a0 a1 a2 z s mu Z
    let law_for = |i: usize, j: usize, read_old: bool| {
        let tys: Vec<Ty> = vec![
            ty!(|_c, _x| sort(2)),
            ty!(|_c, _x| sort(0)),
            ty!(|c, x| { let t = w.sty(c, &[K::W], x[0]); w.g(c, x[1], t) }),
            ty!(|_c, _x| bv_ty(n)),
            ty!(|_c, _x| bv_ty(n)),
            ty!(|_c, _x| bv_ty(n)),
            ty!(|_c, _x| bv_ty(n)),
            ty!(|c, x| c.at(x[0])),
            ty!(|c, x| w.mem(c, x[1])),
            ty!(|c, x| c.at(x[1])),
        ];
        let code = [get(1), konst(1), row("add"), set(i as i64), get(j as i64)];
        law(&tys, move |c, x| {
            let p = w.prog(c, &code, &[], x[0], &[]);
            let p = c.mark(p);
            let restart = restart_via(c, &w, x[1], x[0], x[2], x[7]);
            let me = meaning_env(c, &w, x[1], x[9], restart);
            let slots = [x[3], x[4], x[5], x[6]];
            let fr = var_frame(c, &w, slots, &|_| None);
            let l = app3(w.meaning(c, p, x[2], &me), fr, c.at(x[7]), c.at(x[8]));
            let written = app2(add(n), c.at(x[4]), lit(n, 1));
            let fr2 = var_frame(c, &w, slots, &|s| (s == i).then(|| written.clone()));
            let top = if i == j && !read_old { written.clone() } else { c.at(slots[j]) };
            (refl(l), id(c.at(x[1]), l, app3(c.at(x[2]), fr2, mkpair(c.at(x[0]), top, c.at(x[7])), c.at(x[8]))))
        })
    };
    tatic_kernel::scoped(|| {
        for i in 0..3 {
            for j in 0..3 {
                let (p, s) = law_for(i, j, false);
                ck(&format!("set {i}, get {j}"), &p, &s);
            }
            let (p, s) = law_for(i, i, true);
            assert!(holds(&p, &s).is_err(), "set {i}, get {i} must not read the old slot");
        }
    });
}

/// With a stub `restart` (a bound variable), each list is `[word]` and means `restart fr' mu`: the stack under the `Br`
/// and the code after it are ignored, and `fr'` is the frame at the `Br`, the terminal word included. Restarting on the
/// frame before the write is rejected.
#[test]
fn br_restarts_on_the_current_frame() {
    let t = crate::wasm::table();
    let w = Machine { n: 8, fw: 3, table: t };
    let n = w.n;
    let cases: [(&str, Vec<Ins>, bool); 4] = [
        ("[konst 1, Set 0, konst 9, Br, add]", vec![konst(1), set(0), konst(9), Ins::Br, row("add")], true),
        ("[Br, get 0, add]", vec![Ins::Br, get(0), row("add")], false),
        ("[konst 1, Br, add]", vec![konst(1), Ins::Br, row("add")], false),
        ("[Br]", vec![Ins::Br], false),
    ];
    // S R k restart a0 a1 a2 z s mu Z
    let law_for = |code: &[Ins], writes: bool, old_frame: bool| {
        assert_eq!(out_stack(&t, code, vec![], &[]), vec![K::W], "the list is [word]");
        let tys: Vec<Ty> = vec![
            ty!(|_c, _x| sort(2)),
            ty!(|_c, _x| sort(0)),
            ty!(|c, x| { let t = w.sty(c, &[K::W], x[0]); w.g(c, x[1], t) }),
            ty!(|c, x| { let m = w.mem(c, x[1]); arrow(w.fr(), arrow(m, c.at(x[1]))) }),
            ty!(|_c, _x| bv_ty(n)),
            ty!(|_c, _x| bv_ty(n)),
            ty!(|_c, _x| bv_ty(n)),
            ty!(|_c, _x| bv_ty(n)),
            ty!(|c, x| c.at(x[0])),
            ty!(|c, x| w.mem(c, x[1])),
            ty!(|c, x| c.at(x[1])),
        ];
        let code = code.to_vec();
        law(&tys, move |c, x| {
            let p = w.prog(c, &code, &[], x[0], &[]);
            let p = c.mark(p);
            let me = meaning_env(c, &w, x[1], x[10], x[3]);
            let slots = [x[4], x[5], x[6], x[7]];
            let fr = var_frame(c, &w, slots, &|_| None);
            let l = app3(w.meaning(c, p, x[2], &me), fr, c.at(x[8]), c.at(x[9]));
            let fr2 = var_frame(c, &w, slots, &|s| (writes && !old_frame && s == 0).then(|| lit(n, 1)));
            (refl(l), id(c.at(x[1]), l, app2(c.at(x[3]), fr2, c.at(x[9]))))
        })
    };
    tatic_kernel::scoped(|| {
        for (name, code, writes) in &cases {
            let (p, s) = law_for(code, *writes, false);
            ck(name, &p, &s);
        }
        let (name, code, _) = &cases[0];
        let (p, s) = law_for(code, true, true);
        assert!(holds(&p, &s).is_err(), "{name} must not restart on the frame before the write");
    });
}

/// `[konst 0, konst 1, lt, If([konst 5, Set 0, konst 1], [Br]), get 0, add]` at arity 1 is `[word]` and, with
/// `p0 = 2`, means the word 6: the condition holds, and the then arm's write is what `get 0` reads after the join.
#[test]
fn a_frame_write_flows_across_the_join() {
    let t = crate::wasm::table();
    let w = Machine { n: 8, fw: 1, table: t };
    let n = w.n;
    let code = vec![
        konst(0),
        konst(1),
        row("lt"),
        Ins::If(vec![konst(5), set(0), konst(1)], vec![Ins::Br]),
        get(0),
        row("add"),
    ];
    assert_eq!(out_stack(&t, &code, vec![], &[]), vec![K::W]);
    assert!(shape_check(&t, &[Some(&Entry { arity: 1, env: EnvAccess::Params(0), code: code.clone() })]).is_ok());
    // S R k s mu Z
    let law_for = |answer: u128| {
        let tys: Vec<Ty> = vec![
            ty!(|_c, _x| sort(2)),
            ty!(|_c, _x| sort(0)),
            ty!(|c, x| { let t = w.sty(c, &[K::W], x[0]); w.g(c, x[1], t) }),
            ty!(|c, x| c.at(x[0])),
            ty!(|c, x| w.mem(c, x[1])),
            ty!(|c, x| c.at(x[1])),
        ];
        let code = code.clone();
        law(&tys, move |c, x| {
            let p = w.prog(c, &code, &[], x[0], &[]);
            let p = c.mark(p);
            let restart = restart_via(c, &w, x[1], x[0], x[2], x[3]);
            let me = meaning_env(c, &w, x[1], x[5], restart);
            let l = app3(w.meaning(c, p, x[2], &me), w.frame(&[lit(n, 2)]), c.at(x[3]), c.at(x[4]));
            let want = app3(c.at(x[2]), w.frame(&[lit(n, 5)]), mkpair(c.at(x[0]), lit(n, answer), c.at(x[3])), c.at(x[4]));
            (refl(l), id(c.at(x[1]), l, want))
        })
    };
    tatic_kernel::scoped(|| {
        let (p, s) = law_for(6);
        ck("the write flows across the join: 1 + 5", &p, &s);
        let (p, s) = law_for(3);
        assert!(holds(&p, &s).is_err(), "1 + 2 (the frame before the write) must be rejected");
    });
}
