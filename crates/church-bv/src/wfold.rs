// One proof generator for stream laws over the W-built index of `wnat.rs`: no `shr1` or `mul`, and `lt` only at the root. A pair
// of terms is read through `Machine` and `moore_encoding`, as `machine.rs#tree_proof` reads it at one width, and the proof folds
// over the bit position with `wnat.rs#ind`.
//
// Each pair builds two roots: the proof, lambdas over `operands`, and the statement, `Pi operands. Pi i. root_l i = root_r i`. Both
// build the sides' streams with `side`, and open terms stay inside the root that made them. Inside the proof, each carry's goodness
// and the phi agreement are inductions, each built once and bound as a hypothesis; one position's step goes through `StepProof`,
// shared with `tree_proof`.
//
// The levels. `GoodBool` sits in `Sort2` and a tag splits only into `Sort1`, so a fold state carrying its own goodness cannot pass
// through a tag. None is needed. A carry's goodness is an induction whose telescope binds `GoodBool`'s `P`, `ht` and `hf`, so what
// reaches the tag is `P c`, in `Sort1`; the phi agreement is a `Sigma` of `Id`s, also in `Sort1`. Carries are streams, so each
// one's goodness may use the earlier ones'.
use super::wnat::{add, bw, carry, eqb, good_stream, ind, nw, num, ptw, shl, stream_of, tag_case, xor3, zw, Tag};
use crate::encoding::*;
use crate::machine::{moore_encoding, Encoding, Machine, Src, StepProof};
use crate::rewrite::{Node, Term, ADD, AND, LT, OP_INFO, OR, SHL1, SUB, XOR};
use tatic_kernel::*;

// ---------- a term as streams ----------
fn ones() -> Expr {
    constant(|| Cx::default().lam(nw(), |_, _| t()))
}
/// The stream `\n. body n`.
fn nat_(cx: &mut Cx, body: impl FnOnce(&mut Cx, Expr) -> Expr) -> Expr {
    cx.lam(nw(), |cx, n| {
        let n = cx.at(n);
        body(cx, n)
    })
}
fn at_n(cx: &Cx, s: At, n: Expr) -> Expr {
    app(cx.at(s), n)
}
/// One machine's streams over the operand streams `xs`: the root, and each carry as a stream (a delay cell's carry is the shifted
/// operand).
fn side(cx: &mut Cx, machine: &Machine, xs: &[At]) -> (Expr, Vec<Expr>) {
    let leaf: Vec<At> = machine.leaves.iter().map(|l| match *l.node() {
        Node::V(i) => xs[i],
        Node::Zero => cx.mark(zw()),
        Node::Ones => cx.mark(ones()),
        Node::Op(..) => panic!("an operator as a leaf"),
    }).collect();
    let (mut val, mut carries): (Vec<At>, Vec<Expr>) = (vec![], vec![]);
    for (a, c, o) in machine.nodes.iter() {
        let src = |s: &Src| match s {
            Src::Leaf(j) => leaf[*j],
            Src::Node(j) => val[*j],
        };
        let (p, q) = (src(a), src(c));
        let next = match *o {
            ADD => {
                carries.push(nat_(cx, |cx, n| carry(cx.at(p), cx.at(q), n)));
                add(cx.at(p), cx.at(q))
            }
            AND => nat_(cx, |cx, n| and(at_n(cx, p, n), at_n(cx, q, n))),
            OR => nat_(cx, |cx, n| or(at_n(cx, p, n), at_n(cx, q, n))),
            XOR => nat_(cx, |cx, n| xor(at_n(cx, p, n), at_n(cx, q, n))),
            SUB | LT => {
                // a subtractor's borrow is the carry of `~a` and `b`; an `lt` is the borrow itself, as a stream: its value at `i`
                // compares the low `i` bits (`Machine::step`)
                let not_p = nat_(cx, |cx, n| xor(at_n(cx, p, n), t()));
                let not_p = cx.mark(not_p);
                let borrow = nat_(cx, |cx, n| carry(cx.at(not_p), cx.at(q), n));
                carries.push(borrow);
                let b = cx.mark(borrow);
                if *o == LT { borrow } else { nat_(cx, |cx, n| xor3(at_n(cx, p, n), at_n(cx, q, n), at_n(cx, b, n))) }
            }
            SHL1 => {
                carries.push(shl(cx.at(p)));
                shl(cx.at(p))
            }
            _ => panic!("no stream for {}", OP_INFO[*o].name),
        };
        val.push(cx.mark(next));
    }
    let root = match machine.root {
        Src::Leaf(j) => leaf[j],
        Src::Node(j) => val[j],
    };
    (cx.at(root), carries)
}

// ---------- conjunctions ----------
/// `body` one binder deeper, given `ts` there: a `Sigma` family whose second component does not depend on the first.
fn fam(cx: &mut Cx, ts: &[Expr], body: impl FnOnce(&mut Cx, &[Expr]) -> Expr) -> Expr {
    let ts: Vec<At> = ts.iter().map(|t| cx.mark(*t)).collect();
    cx.under(|cx, _| {
        let ts: Vec<Expr> = ts.iter().map(|t| cx.at(*t)).collect();
        body(cx, &ts)
    })
}
/// The conjunction of `ts`, a right-nested `Sigma`.
fn sigmas(cx: &mut Cx, ts: &[Expr]) -> Expr {
    let [a, rest @ ..] = ts else { panic!("an empty conjunction") };
    if rest.is_empty() {
        return *a;
    }
    let tail = fam(cx, rest, sigmas);
    sigma(*a, tail)
}
/// A proof of `sigmas(ts)` from a proof `ps[q]` of each `ts[q]`.
fn pack(cx: &mut Cx, ts: &[Expr], ps: &[Expr]) -> Expr {
    match ps {
        [p] => *p,
        [p, rest @ ..] => {
            let tail = fam(cx, &ts[1..], sigmas);
            let r = pack(cx, &ts[1..], rest);
            pair(tail, *p, r)
        }
        [] => panic!("an empty conjunction"),
    }
}
/// Every component of a proof `t` of `sigmas(ts)`.
fn unpack(cx: &mut Cx, ts: &[Expr], t: Expr) -> Vec<Expr> {
    let [a, rest @ ..] = ts else { panic!("an empty conjunction") };
    if rest.is_empty() {
        return vec![t];
    }
    let (a, whole, tail) = (*a, sigmas(cx, ts), sigmas(cx, rest));
    let tail_at = cx.mark(tail);
    let take = |cx: &mut Cx, left: bool| {
        let motive = lam(whole, fam(cx, &[if left { a } else { tail }], |_, r| r[0]));
        let step = cx.lam(a, |cx, l| {
            let tail = cx.at(tail_at);
            cx.lam(tail, |cx, r| cx.at(if left { l } else { r }))
        });
        sigrec(motive, step, t)
    };
    let mut out = vec![take(cx, true)];
    let right = take(cx, false);
    out.extend(unpack(cx, rest, right));
    out
}

// ---------- the law ----------
/// The two terms' machines and their encoding, if the law has one.
fn encode(k: usize, t1: &Term, t2: &Term) -> Option<([Machine; 2], Encoding)> {
    let machines = [Machine::parse(t1)?, Machine::parse(t2)?];
    let enc = moore_encoding(&machines[0], &machines[1], k)?;
    Some((machines, enc))
}
/// A law's telescope: the operand streams `x_i`, then their goodness `g_i : good_stream x_i`.
fn operands(k: usize) -> Vec<Ty<'static>> {
    let xs = (0..k).map(|_| ty!(|_c, _x| bw()));
    let gs = (0..k).map(|i| ty!(|c, x| good_stream(c, c.at(x[i]))));
    xs.chain(gs).collect()
}
/// The phi agreement of two sides' carries `l` and `r`: `phi_q l = phi_q r` for each `q`.
fn agree(sp: &StepProof, l: &[Expr], r: &[Expr]) -> Vec<Expr> {
    (0..sp.enc.phi[0].len()).map(|q| eqb(sp.phi(0, q, l), sp.phi(1, q, r))).collect()
}
/// The proof root's streams, at the depth of `operands`: the operands and their witnesses, each side's carries, and the side lemmas.
struct Root<'r, 'a> {
    sp: &'r StepProof<'a>,
    xs: &'r [At],
    carries: [Vec<At>; 2],
    lemmas: &'r [Vec<Expr>],
}
impl Root<'_, '_> {
    fn carries_at(&self, cx: &Cx, sd: usize, p: Expr) -> Vec<Expr> {
        self.carries[sd].iter().map(|c| app(cx.at(*c), p)).collect()
    }
    /// A side's next carries from position `p`.
    fn next(&self, cx: &Cx, sd: usize, p: Expr) -> Vec<Expr> {
        let ops = self.xs[..self.sp.k].iter().map(|x| app(cx.at(*x), p));
        self.sp.step_of(sd, &ops.chain(self.carries_at(cx, sd, p)).collect::<Vec<_>>()).1
    }
    /// The operand bits at `p` with their witnesses.
    fn ug(&self, cx: &Cx, p: Expr) -> Vec<Gb> {
        let k = self.sp.k;
        (0..k).map(|i| Gb { e: app(cx.at(self.xs[i]), p), g: app(cx.at(self.xs[k + i]), p) }).collect()
    }
    /// A side's carries at `p`, carry `d` with the witness `good(d)`.
    fn st(&self, cx: &Cx, sd: usize, p: Expr, good: &dyn Fn(usize) -> Expr) -> Vec<Gb> {
        self.carries_at(cx, sd, p).into_iter().enumerate().map(|(d, e)| Gb { e, g: good(d) }).collect()
    }
    /// `F_j` of the left at `p` equals the right's, from the carries' goodness `goods` and the phi agreement `ip` at `p`.
    fn eq(&self, cx: &Cx, goods: &[Vec<At>; 2], j: usize, p: Expr, ip: &[Expr]) -> Expr {
        let st = [0, 1].map(|sd| self.st(cx, sd, p, &|d| app(cx.at(goods[sd][d]), p)));
        self.sp.eq(j, [&self.lemmas[0][j], &self.lemmas[1][j]], &self.ug(cx, p), [&st[0], &st[1]], ip).2
    }
}
/// `Pi n. GoodBool (carry n)` for side `sd`'s carry `c`, by induction on `n` under the earlier carries' goodness `done`, and that
/// type.
fn good_carry(cx: &mut Cx, r: &Root, sd: usize, c: usize, done: &[At]) -> (Expr, Expr) {
    let cc = r.carries[sd][c];
    let ty = cx.pi(nw(), |cx, n| app(good_bool(), app(cx.at(cc), cx.at(n))));
    // `GoodBool`'s binders `P`, `ht`, `hf`
    let tys = [ty!(|_c, _x| arrow(bool0(), sort(1))), ty!(|c, x| app(c.at(x[0]), t())), ty!(|c, x| app(c.at(x[0]), f()))];
    let body = |cx: &mut Cx, n: Expr, ps: &[At]| app(cx.at(ps[0]), app(cx.at(cc), n));
    let pred = |cx: &mut Cx, tag: &Tag, ps: &[At]| {
        let e = tag_case(cx, tag, &|cx, p, _| r.next(cx, sd, p)[c], f());
        app(cx.at(ps[0]), e)
    };
    let hj = |cx: &mut Cx, p: Expr, ih: Expr, ps: &[At]| {
        // a carry reads only the earlier ones, so a later one's witness is never used
        let st = r.st(cx, sd, p, &|d| match d {
            _ if d < c => app(cx.at(done[d]), p),
            _ if d == c => ih,
            _ => f(),
        });
        let g = r.sp.machines[sd].step(&r.sp.gops, &r.ug(cx, p), &st).1[c].g;
        app3(g, cx.at(ps[0]), cx.at(ps[1]), cx.at(ps[2]))
    };
    let hn = |cx: &mut Cx, ps: &[At]| cx.at(ps[2]);
    let proof = cx.lam(nw(), |cx, n| ind(cx, &tys, &body, cx.at(n), &pred, &hj, &hn));
    (proof, ty)
}
/// `rest` under every carry's goodness, each proved under the earlier ones of its side and bound once: `(\h:ty. rest) proof`.
fn with_goods(cx: &mut Cx, r: &Root, goods: &mut [Vec<At>; 2], rest: &mut dyn FnMut(&mut Cx, &[Vec<At>; 2]) -> Expr) -> Expr {
    let Some(sd) = (0..2).find(|&sd| goods[sd].len() < r.carries[sd].len()) else { return rest(cx, goods) };
    let (proof, ty) = good_carry(cx, r, sd, goods[sd].len(), &goods[sd]);
    let body = cx.lam(ty, |cx, h| {
        goods[sd].push(h);
        let b = with_goods(cx, r, goods, rest);
        goods[sd].pop();
        b
    });
    app(body, proof)
}
/// `Pi n. sigmas(agree n)`: the sides' phi values agree at every position, by induction on `n`, and that type.
fn invariant(cx: &mut Cx, r: &Root, goods: &[Vec<At>; 2]) -> (Expr, Expr) {
    let m = r.sp.enc.phi[0].len();
    let body = |cx: &mut Cx, n: Expr, _: &[At]| {
        let ts = agree(r.sp, &r.carries_at(cx, 0, n), &r.carries_at(cx, 1, n));
        sigmas(cx, &ts)
    };
    let ty = cx.pi(nw(), |cx, n| body(cx, cx.at(n), &[]));
    let pred = |cx: &mut Cx, tag: &Tag, _: &[At]| {
        let mut reduced = |sd: usize| -> Vec<Expr> {
            (0..r.carries[sd].len()).map(|d| tag_case(cx, tag, &|cx, p, _| r.next(cx, sd, p)[d], f())).collect()
        };
        let (l, rr) = (reduced(0), reduced(1));
        let ts = agree(r.sp, &l, &rr);
        sigmas(cx, &ts)
    };
    let hj = |cx: &mut Cx, p: Expr, ih: Expr, _: &[At]| {
        let at_p = agree(r.sp, &r.carries_at(cx, 0, p), &r.carries_at(cx, 1, p));
        let ip = unpack(cx, &at_p, ih);
        let ts = agree(r.sp, &r.next(cx, 0, p), &r.next(cx, 1, p));
        let ps: Vec<Expr> = (1..=m).map(|j| r.eq(cx, goods, j, p, &ip)).collect();
        pack(cx, &ts, &ps)
    };
    let hn = |cx: &mut Cx, _: &[At]| {
        let start = |sd: usize| vec![f(); r.carries[sd].len()];
        let ts = agree(r.sp, &start(0), &start(1));
        // the initial phi values agree by evaluation
        let ps: Vec<Expr> = (0..m).map(|q| refl(r.sp.phi(0, q, &start(0)))).collect();
        pack(cx, &ts, &ps)
    };
    let proof = cx.lam(nw(), |cx, n| ind(cx, &[], &body, cx.at(n), &pred, &hj, &hn));
    (proof, ty)
}
/// The proof of the law two machines compute, and its statement. Its caller builds and checks it in one `scoped` region.
fn proof(k: usize, machines: &[Machine; 2], enc: &Encoding) -> (Expr, Expr) {
    assert!(intern_generation() != 0, "wfold::proof outside a scoped region: build and check it in one tatic_kernel::scoped call");
    let sp = StepProof::new(machines, enc, k);
    let lemmas: Vec<Vec<Expr>> = (0..2).map(|sd| (0..=enc.phi[0].len()).map(|j| sp.lemma(sd, j).0).collect()).collect();
    let stmt = |cx: &mut Cx, xs: &[At]| {
        let (l, r) = (side(cx, &machines[0], &xs[..k]).0, side(cx, &machines[1], &xs[..k]).0);
        ptw(cx, l, r)
    };
    law(&operands(k), stmt, |cx, xs| {
        let carries = [0, 1].map(|sd| {
            let cs = side(cx, &machines[sd], &xs[..k]).1;
            cs.into_iter().map(|c| cx.mark(c)).collect()
        });
        let r = Root { sp: &sp, xs, carries, lemmas: &lemmas };
        with_goods(cx, &r, &mut [vec![], vec![]], &mut |cx, goods| {
            let (inv, ty) = invariant(cx, &r, goods);
            let body = cx.lam(ty, |cx, h| cx.lam(nw(), |cx, i| {
                let i = cx.at(i);
                let ts = agree(r.sp, &r.carries_at(cx, 0, i), &r.carries_at(cx, 1, i));
                let ip = unpack(cx, &ts, app(cx.at(h), i));
                r.eq(cx, goods, 0, i, &ip)
            }));
            app(body, inv)
        })
    })
}

fn op2(o: usize) -> impl Fn(Term, Term) -> Term {
    move |a, c| Term::op(o, a, c)
}
fn shl_t(a: Term) -> Term {
    Term::op(SHL1, a, Term::ZERO)
}
fn proved(k: usize, l: Term, r: Term) {
    let name = format!("{} = {}", l.show(), r.show());
    let (machines, enc) = encode(k, &l, &r).unwrap_or_else(|| panic!("{name}: no encoding"));
    tatic_kernel::scoped(|| {
        let (proof, stmt) = proof(k, &machines, &enc);
        checked(&name, check(&Ctx::new(), &proof, &stmt));
    })
}
/// `ty`'s first `args.len()` Pis turned back into lambdas around the rest, applied to `args` (`def_eq` does the beta steps).
fn instance(ty: &Expr, args: &[Expr]) -> Expr {
    fn open(ty: &Expr, n: usize) -> Expr {
        if n == 0 {
            return *ty;
        }
        let tatic_kernel::Node::Pi(d, b) = ty.node() else { panic!("fewer Pis than arguments") };
        lam(d, open(&b, n - 1))
    }
    apps(open(ty, args.len()), args.to_vec())
}

/// The statement is about wnat's own `add`, and a proof proves only its own law.
#[test]
fn w_fold_add_associates() {
    let (x, y, z, plus) = (Term::v(0), Term::v(1), Term::v(2), op2(ADD));
    let (machines, enc) = encode(3, &plus(plus(x, y), z), &plus(x, plus(y, z))).unwrap();
    tatic_kernel::scoped(|| {
        let (proof, stmt) = proof(3, &machines, &enc);
        checked("(x + y) + z = x + (y + z)", check(&Ctx::new(), &proof, &stmt));
        let by_hand = |r: &dyn Fn(Expr, Expr, Expr) -> Expr| statement(&operands(3), |cx, xs| {
            let [a, c, d] = [0, 1, 2].map(|i| cx.at(xs[i]));
            ptw(cx, add(add(a, c), d), r(a, c, d))
        });
        assert!(def_eq(&stmt, &by_hand(&|a, c, d| add(a, add(c, d)))), "not the law as written");
        assert!(check(&Ctx::new(), &proof, &by_hand(&|a, c, _| add(a, add(c, c)))).is_err(), "control: (x + y) + z = x + (y + y)");
    })
}
#[test]
fn w_fold_a_false_table_is_rejected() {
    let (x, y, z, plus) = (Term::v(0), Term::v(1), Term::v(2), op2(ADD));
    let (machines, mut enc) = encode(3, &plus(plus(x, y), z), &plus(x, plus(y, z))).unwrap();
    enc.g[1][0] = !enc.g[1][0];
    tatic_kernel::scoped(|| {
        let (proof, stmt) = proof(3, &machines, &enc);
        assert!(check(&Ctx::new(), &proof, &stmt).is_err(), "control: a flipped table bit");
    });
    assert!(encode(2, &plus(x, y), &x).is_none(), "a false law has no encoding");
}
#[test]
fn w_fold_the_law_families() {
    let (x, y, z, w) = (Term::v(0), Term::v(1), Term::v(2), Term::v(3));
    let (add, sub, and, or, xor, lt) = (op2(ADD), op2(SUB), op2(AND), op2(OR), op2(XOR), op2(LT));
    proved(2, add(x, y), add(y, x));
    proved(1, add(x, Term::ZERO), x);
    proved(4, add(add(x, y), add(z, w)), add(add(x, z), add(y, w)));
    proved(2, sub(x, x), Term::ZERO);
    proved(2, sub(add(x, y), y), x);
    proved(3, sub(x, add(y, z)), sub(sub(x, y), z));
    proved(2, add(and(x, y), or(x, y)), add(x, y));
    proved(2, add(xor(x, y), shl_t(and(x, y))), add(x, y));
    proved(2, shl_t(add(x, y)), add(shl_t(x), shl_t(y)));
    proved(1, add(x, x), shl_t(x));
    proved(3, and(x, or(y, z)), or(and(x, y), and(x, z)));
    proved(2, xor(xor(x, y), y), x);
    proved(1, lt(x, x), lt(Term::ZERO, Term::ZERO));
    proved(2, lt(add(x, y), add(x, y)), lt(x, x));
    proved(2, lt(xor(x, y), xor(y, x)), lt(y, y));
    proved(2, lt(x, y), lt(xor(y, Term::ONES), xor(x, Term::ONES)));
    proved(2, lt(x, y), lt(add(x, Term::ZERO), or(y, y)));
}
/// A theorem's hypotheses hold of real streams: at all-ones and all-zeros operands and a position, it gives that bit of the words
/// (of the comparison, for a root `lt`), and a witness paired with the wrong stream is rejected.
#[test]
fn w_fold_a_theorem_applies_to_good_streams() {
    let (x, y, z) = (Term::v(0), Term::v(1), Term::v(2));
    let (sub, plus, and, or, xor, lt) = (op2(SUB), op2(ADD), op2(AND), op2(OR), op2(XOR), op2(LT));
    let not = |a: Term| xor(a, Term::ONES);
    let n = 3;
    let start = std::time::Instant::now();
    for (k, l, r) in [(3, sub(x, plus(y, z)), sub(sub(x, y), z)), (2, lt(x, y), lt(not(y), not(x))), (2, and(x, or(x, y)), x)] {
        tatic_kernel::scoped(|| {
            let (machines, enc) = encode(k, &l, &r).unwrap();
            let (proof, _) = proof(k, &machines, &enc);
            let ty = infer(&Ctx::new(), &proof).unwrap();
            let cmp = match *l.node() {
                Node::Op(LT, a, c) => Some((a, c)),
                _ => None,
            };
            // a word's bit `p` of `l`, or a root `lt`'s comparison of the low `p` bits, operand `i` all-ones iff `ones_at(i)`
            let e = |ones_at: &dyn Fn(usize) -> bool, p: usize| -> bool {
                let vals: Vec<u128> = (0..k).map(|i| if ones_at(i) { 7 } else { 0 }).collect();
                match cmp {
                    Some((a, c)) => {
                        let low = (1u128 << p) - 1;
                        a.interp(n, &vals) & low < c.interp(n, &vals) & low
                    }
                    None => (l.interp(n, &vals) >> p) & 1 == 1,
                }
            };
            let args = |ones_at: &dyn Fn(usize) -> bool, p: usize| -> Vec<Expr> {
                let streams = (0..k).map(|i| if ones_at(i) { ones() } else { zw() });
                let goods = (0..k).map(|i| Cx::default().lam(nw(), |_, _| good_bit(ones_at(i))));
                streams.chain(goods).chain([num(p)]).collect()
            };
            let last = if cmp.is_some() { n } else { n - 1 };
            for assign in 0..1usize << k {
                let ones_at = |i: usize| (assign >> i) & 1 == 1;
                for p in [0, last] {
                    let (e, inst) = (e(&ones_at, p), instance(&ty, &args(&ones_at, p)));
                    assert!(def_eq(&inst, &eqb(bit(e), bit(e))), "{} at {assign:b} bit {p}", l.show());
                    assert!(!def_eq(&inst, &eqb(bit(!e), bit(!e))), "{} at {assign:b} bit {p}: the wrong bit", l.show());
                }
            }
            let mixed = |i: usize| i % 2 == 0;
            let (e, mut args) = (e(&mixed, last), args(&mixed, last));
            checked(&l.show(), check(&Ctx::new(), &apps(proof, args.clone()), &eqb(bit(e), bit(e))));
            args.swap(k, k + 1);
            assert!(check(&Ctx::new(), &apps(proof, args), &eqb(bit(e), bit(e))).is_err(), "{}: a mispaired witness", l.show());
        });
    }
    println!("w_fold_a_theorem_applies_to_good_streams: {} ms", start.elapsed().as_millis());
}
/// The proof's inferred type is the statement, and no larger than twice its size: a goodness proof leaking into a type would show.
#[test]
fn w_fold_proof_type_is_the_statement() {
    let (x, y, z, plus) = (Term::v(0), Term::v(1), Term::v(2), op2(ADD));
    let (machines, enc) = encode(3, &plus(plus(x, y), z), &plus(x, plus(y, z))).unwrap();
    tatic_kernel::scoped(|| {
        let (proof, stmt) = proof(3, &machines, &enc);
        let ty = infer(&Ctx::new(), &proof).unwrap();
        assert!(def_eq(&ty, &stmt), "the inferred type is not the statement");
        let (p, t, s) = (term_sizes(&proof), term_sizes(&ty), term_sizes(&stmt));
        println!("term_sizes (distinct, tree): proof {p:?} type {t:?} statement {s:?}");
        assert!(t.0 <= 2 * s.0, "the inferred type has {} nodes against the statement's {}", t.0, s.0);
    })
}
/// A comparison that varies: its proof proves only its own law, and swapped operands have no encoding.
#[test]
fn w_fold_a_comparison_is_its_own_law() {
    let (x, y, lt, xor) = (Term::v(0), Term::v(1), op2(LT), op2(XOR));
    let (machines, enc) = encode(2, &lt(x, y), &lt(xor(y, Term::ONES), xor(x, Term::ONES))).unwrap();
    tatic_kernel::scoped(|| {
        let (proof, stmt) = proof(2, &machines, &enc);
        checked("x < y = ~y < ~x", check(&Ctx::new(), &proof, &stmt));
        let (left, swapped) = (Machine::parse(&lt(x, y)).unwrap(), Machine::parse(&lt(y, x)).unwrap());
        let wrong = statement(&operands(2), |cx, xs| {
            let (l, r) = (side(cx, &left, &xs[..2]).0, side(cx, &swapped, &xs[..2]).0);
            ptw(cx, l, r)
        });
        assert!(check(&Ctx::new(), &proof, &wrong).is_err(), "control: x < y = y < x");
    });
    assert!(encode(2, &lt(x, y), &lt(y, x)).is_none(), "a false comparison has no encoding");
}
/// An `lt`'s stream is its borrow: below the root its parent would read the borrow as a word, and a root `lt` is no word.
#[test]
fn w_fold_lt_outside_the_root_has_no_law() {
    let (x, y, z, add, sub, lt) = (Term::v(0), Term::v(1), Term::v(2), op2(ADD), op2(SUB), op2(LT));
    assert!(encode(3, &add(lt(x, y), z), &add(sub(x, y), z)).is_none(), "lt read as sub");
    assert!(encode(3, &add(lt(x, y), z), &add(z, lt(x, y))).is_none(), "lt below the root");
    assert!(encode(3, &lt(lt(x, y), z), &lt(lt(x, y), z)).is_none(), "lt under a root lt");
    assert!(encode(1, &lt(x, x), &Term::ZERO).is_none(), "a root lt against a word");
}
/// A law says only what its streams compute: at closed operands they give the words, and a root `lt` at `p` compares the low `p` bits.
#[test]
fn w_fold_streams_compute_the_words() {
    let nb = 3;
    let (x, y, add, sub) = (Term::v(0), Term::v(1), op2(ADD), op2(SUB));
    let terms = [add(x, y), sub(x, y), op2(AND)(x, y), op2(OR)(x, y), op2(XOR)(x, y), shl_t(x), sub(add(x, x), shl_t(y)), Term::ONES];
    for (a, c) in [(5u128, 3u128), (7, 7), (6, 1), (0, 5), (2, 6)] {
        let mut cx = Cx::default();
        let xs = [cx.mark(stream_of(a, nb)), cx.mark(stream_of(c, nb))];
        for t in &terms {
            let root = side(&mut cx, &Machine::parse(t).unwrap(), &xs).0;
            for p in 0..nb {
                let want = bit((t.interp(nb, &[a, c]) >> p) & 1 == 1);
                assert!(def_eq(&app(root, num(p)), &want), "{}: {a} {c} bit {p}", t.show());
            }
        }
        let root = side(&mut cx, &Machine::parse(&op2(LT)(x, y)).unwrap(), &xs).0;
        for p in 0..=nb {
            let low = (1u128 << p) - 1;
            assert!(def_eq(&app(root, num(p)), &bit(a & low < c & low)), "lt {a} {c} at {p}");
        }
    }
}
/// Equal terms over `x`, `y` and two operator levels, and comparisons of one-level terms, sampled by a stride: every pair
/// gets an accepted proof, or differs at some other width. Cadence: the suite runs the default stride (11 pairs); counts
/// and profiles use `WFOLD_STRIDE=97` (470 pairs); the full sweep (`WFOLD_STRIDE=1 WFOLD_THREADS=10`, all 45677 pairs,
/// about 36 s) runs through `run.ps1 -Kind sweep` before a tag and after any change to this file, `wnat.rs`, the encoding
/// search in `machine.rs` or the kernel.
#[test]
fn w_fold_every_encoded_pair() {
    let stride: usize = crate::Setup::process().or("WFOLD_STRIDE", 4001);
    let (n, mask) = (4, 15u128);
    let atoms = [Term::v(0), Term::v(1), Term::ZERO, Term::ONES];
    let level = |ts: &[Term]| -> Vec<Term> {
        let bin = ts.iter().flat_map(|a| ts.iter().flat_map(move |c| [ADD, SUB, AND, OR, XOR].map(|o| Term::op(o, *a, *c))));
        ts.iter().copied().chain(bin).chain(ts.iter().map(|a| shl_t(*a))).collect()
    };
    let one = level(&atoms);
    let lts = one.iter().flat_map(|a| one.iter().map(move |c| Term::op(LT, *a, *c)));
    let mut first: hashbrown::HashMap<(bool, Vec<u128>), Term> = Default::default();
    let (mut pairs, mut sampled) = (0usize, vec![]);
    for t in level(&one).into_iter().chain(lts) {
        let words = (0..=mask).flat_map(|x| (0..=mask).map(move |y| (x, y))).map(|(x, y)| t.interp(n, &[x, y])).collect();
        let sig = (matches!(*t.node(), Node::Op(LT, ..)), words);
        let Some(r) = first.get(&sig).copied() else {
            first.insert(sig, t);
            continue;
        };
        if r == t {
            continue;
        }
        pairs += 1;
        if pairs % stride == 0 {
            sampled.push((t, r));
        }
    }
    // each sampled pair is built and checked in its own region, round robin over `WFOLD_THREADS` workers (at most 10; terms
    // are per thread); true when it was proved, false when it has no encoding
    let prove = |t: Term, r: Term| -> bool {
        let Some((machines, enc)) = encode(2, &t, &r) else {
            // the classes are by width 4 only: a pair with no encoding must differ at another width
            let differ = |n: u32| {
                let m = (1u128 << n) - 1;
                (0..=m).flat_map(|x| (0..=m).map(move |y| (x, y))).find(|(x, y)| t.interp(n as usize, &[*x, *y]) != r.interp(n as usize, &[*x, *y])).map(|w| (n, w))
            };
            let witness = (1..=6).find_map(differ).unwrap_or_else(|| panic!("{} = {}: no encoding, yet equal at widths 1 to 6", t.show(), r.show()));
            println!("no encoding: {} = {}, differ at {witness:?}", t.show(), r.show());
            return false;
        };
        let (proof, stmt) = proof(2, &machines, &enc);
        checked(&format!("{} = {}", t.show(), r.show()), check(&Ctx::new(), &proof, &stmt));
        true
    };
    let threads = crate::Setup::process().or("WFOLD_THREADS", 1usize).clamp(1, 10);
    let proved: Vec<bool> = std::thread::scope(|sc| {
        let (sampled, prove) = (&sampled, &prove);
        let workers: Vec<_> = (0..threads).map(|w| std::thread::Builder::new().stack_size(256 << 20).spawn_scoped(sc, move || {
            sampled.iter().skip(w).step_by(threads).map(|&(t, r)| tatic_kernel::scoped(|| prove(t, r))).collect::<Vec<_>>()
        }).unwrap()).collect();
        workers.into_iter().flat_map(|h| h.join().unwrap()).collect()
    });
    let tried = proved.iter().filter(|p| **p).count();
    println!("pairs={pairs} stride={stride} threads={threads} tried={tried} no-encoding={}", proved.len() - tried);
    assert!(tried > 0);
}
