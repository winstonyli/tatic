//! The loop form's machine parts: `local.set` (the `Set` class) writes one parameter slot of the frame.
use super::tests::{konst, row};
use super::*;

/// The test's `MeaningEnv` at the answer type `r`: no `choose` and the environment of no functions (a call answers 0
/// at the memory it was given).
fn meaning_env(c: &mut Cx, w: &Machine, r: At) -> MeaningEnv {
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
    MeaningEnv { r, ch: None, calls: none }
}

/// Over a hand-built frame of variables (three slots and the terminal word, so a clobbered word shows, where
/// `Machine::frame`'s literal zeros would hide it), `[get 1, konst 1, add, Set i, get j]` hands the continuation the
/// frame with slot `i` replaced by `a1 + 1`, and pushes that word when `i == j` and slot `j`'s variable otherwise.
/// Reading the old slot after a write is rejected.
#[test]
fn local_set_writes_one_slot() {
    let t = crate::wasm::table();
    let w = Machine { n: 8, fw: 3, table: &t };
    let n = w.n;
    let get = |i| Ins::Row { name: "local.get", operand: i };
    let set = |i| Ins::Row { name: "local.set", operand: i };
    // the frame `(a0, (a1, (a2, z)))` of variables `x[3..7]`
    let frame = |c: &Cx, s: [At; 4]| {
        (0..3).rev().fold(c.at(s[3]), |acc, i| mkpair(w.words(2 - i, w.v()), c.at(s[i]), acc))
    };
    // S R k a0 a1 a2 z s mu
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
        ];
        let code = [get(1), konst(1), row("add"), set(i as i64), get(j as i64)];
        law(&tys, move |c, x| {
            let p = w.prog(c, &code, &[], x[0], &[]);
            let p = c.mark(p);
            let me = meaning_env(c, &w, x[1]);
            let slots = [x[3], x[4], x[5], x[6]];
            let fr = frame(c, slots);
            let l = app3(w.meaning(c, p, x[2], &me), fr, c.at(x[7]), c.at(x[8]));
            let written = app2(add(n), c.at(x[4]), lit(n, 1));
            // the frame after the write, built by hand: slot `i` is the written word
            let fr2 = (0..3).rev().fold(c.at(x[6]), |acc, s| {
                let word = if s == i { written.clone() } else { c.at(slots[s]) };
                mkpair(w.words(2 - s, w.v()), word, acc)
            });
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
