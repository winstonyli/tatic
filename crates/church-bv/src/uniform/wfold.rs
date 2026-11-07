// Spike (2026-11-07, q2): one proof generator for stream laws (no `shr1` or `mul`, `lt` only at the root), over the W-built index of `wnat.rs`. It reads a
// pair of terms through `Machine` and `moore_encoding`, as `machine.rs#tree_proof` does at one width, and folds over the position.
//
// The levels. `GoodBool` sits in `Sort2` and a tag splits only into `Sort1`, so a fold state carrying its own goodness cannot pass
// through a tag. None is needed. Goodness of a carry is its own induction with `P` bound by `ind`'s `pre`, so what reaches the tag
// is `P c`, in `Sort1`; the phi agreement is a `Sigma` of `Id`s, also in `Sort1`. Carries are streams, so each one's goodness may
// use the earlier ones'.
use super::mul::bit_of;
use super::width::T::*;
use super::width::*;
use super::wnat::{add as add_w, *};
use crate::machine::{index_of, moore_encoding, Encoding, Machine, Src};
use crate::rewrite::{Node, Term, ADD, AND, LT, OP_INFO, OR, SHL1, SUB, XOR};
use crate::search::Gates;

const XS: [&str; 4] = ["x0", "x1", "x2", "x3"];
const GS: [&str; 4] = ["g0", "g1", "g2", "g3"];
const CB: [&str; 12] = ["$b0", "$b1", "$b2", "$b3", "$b4", "$b5", "$b6", "$b7", "$b8", "$b9", "$b10", "$b11"];
const CG: [&str; 12] = ["$g0", "$g1", "$g2", "$g3", "$g4", "$g5", "$g6", "$g7", "$g8", "$g9", "$g10", "$g11"];

/// `Machine::step` on terms.
struct Terms;
impl Gates for Terms {
    type S = T;
    fn and(&self, x: &T, y: &T) -> T {
        and2(x.clone(), y.clone())
    }
    fn or(&self, x: &T, y: &T) -> T {
        or2(x.clone(), y.clone())
    }
    fn xor(&self, x: &T, y: &T) -> T {
        xor(x.clone(), y.clone())
    }
    fn konst(&self, b: bool) -> T {
        if b { tt() } else { ff() }
    }
}

/// A bit and its `GoodBool` witness.
#[derive(Clone)]
struct Good {
    e: T,
    g: T,
}
fn p_of(e: T) -> T {
    ap(v("$P"), e)
}
fn pick(b: bool) -> T {
    v(if b { "$ht" } else { "$hf" })
}
/// The lambdas of a `GoodBool` proof: `$P`, `$ht`, `$hf` are in scope in `t`.
fn good_lams(t: T) -> T {
    lm("$P", arr(bool0(), s(1)), lm("$ht", p_of(tt()), lm("$hf", p_of(ff()), t)))
}
fn gate(op: usize, f: fn(T, T) -> T, x: &Good, y: &Good) -> Good {
    let truth = OP_INFO[op].truth;
    let arm = |a: bool| {
        let av = Terms.konst(a);
        ap3(y.g.clone(), lm("$b", bool0(), p_of(f(av, v("$b")))), pick(truth(a, true)), pick(truth(a, false)))
    };
    let body = ap3(x.g.clone(), lm("$a", bool0(), p_of(f(v("$a"), y.e.clone()))), arm(true), arm(false));
    Good { e: f(x.e.clone(), y.e.clone()), g: good_lams(body) }
}
/// `Machine::step` on bits with their witnesses.
struct Goods;
impl Gates for Goods {
    type S = Good;
    fn and(&self, x: &Good, y: &Good) -> Good {
        gate(1, and2, x, y)
    }
    fn or(&self, x: &Good, y: &Good) -> Good {
        gate(2, or2, x, y)
    }
    fn xor(&self, x: &Good, y: &Good) -> Good {
        gate(3, xor, x, y)
    }
    fn konst(&self, b: bool) -> Good {
        Good { e: Terms.konst(b), g: good_lams(pick(b)) }
    }
}

// ---------- a term as streams ----------
fn ones() -> T {
    lm("$i", nw(), tt())
}
fn nat_(e: T) -> T {
    lm("$n", nw(), e)
}
fn at_n(s: &T) -> T {
    ap(s.clone(), v("$n"))
}
/// One machine's streams: the root, and each carry as a stream (a delay cell's carry is the shifted operand).
struct Side {
    m: Machine,
    root: T,
    carries: Vec<T>,
}
fn side(t: &Term, x: &[T]) -> Side {
    let m = Machine::parse(t).expect("a machine");
    let leaf: Vec<T> = m.leaves.iter().map(|l| match *l.node() {
        Node::V(i) => x[i].clone(),
        Node::Zero => zw(),
        Node::Ones => ones(),
        Node::Op(..) => panic!("an operator as a leaf"),
    }).collect();
    let (mut val, mut carries): (Vec<T>, Vec<T>) = (vec![], vec![]);
    for (a, c, o) in m.nodes.iter() {
        let src = |s: &Src| match s {
            Src::Leaf(j) => leaf[*j].clone(),
            Src::Node(j) => val[*j].clone(),
        };
        let (p, q) = (src(a), src(c));
        let next = match o {
            0 => {
                carries.push(nat_(carry(p.clone(), q.clone(), v("$n"))));
                add_w(p, q)
            }
            1 => nat_(and2(at_n(&p), at_n(&q))),
            2 => nat_(or2(at_n(&p), at_n(&q))),
            3 => nat_(xor(at_n(&p), at_n(&q))),
            4 | 5 => {
                // a subtractor's borrow is the carry of `~a` and `b`; an `lt` here is the root (`Machine::streams`)
                let borrow = nat_(carry(nat_(xor(at_n(&p), tt())), q.clone(), v("$n")));
                carries.push(borrow.clone());
                nat_(xor3(at_n(&p), at_n(&q), at_n(&borrow)))
            }
            6 => {
                carries.push(shl(p.clone()));
                shl(p)
            }
            _ => panic!("no stream for {}", OP_INFO[*o].name),
        };
        val.push(next);
    }
    let root = match m.root {
        // a root `lt` is the last borrow, as a stream: its value at `i` compares the low `i` bits
        _ if m.last() => carries.last().expect("a borrow").clone(),
        Src::Leaf(j) => leaf[j].clone(),
        Src::Node(j) => val[j].clone(),
    };
    Side { m, root, carries }
}

// ---------- tables, case trees, conjunctions ----------
fn mux(c: T, a: T, d: T) -> T {
    lm("$C", s(0), lm("$t", v("$C"), lm("$e", v("$C"), ap3(c, v("$C"), ap3(a, v("$C"), v("$t"), v("$e")), ap3(d, v("$C"), v("$t"), v("$e"))))))
}
/// The Boolean function `f` applied to the bits `s`, first most significant.
fn table(s: &[T], f: &dyn Fn(&[bool]) -> bool) -> T {
    fn go(s: &[T], pre: &mut Vec<bool>, f: &dyn Fn(&[bool]) -> bool) -> T {
        if pre.len() == s.len() {
            return Terms.konst(f(pre));
        }
        let c = s[pre.len()].clone();
        pre.push(true);
        let a = go(s, pre, f);
        pre.pop();
        pre.push(false);
        let d = go(s, pre, f);
        pre.pop();
        mux(c, a, d)
    }
    go(s, &mut vec![], f)
}
/// `Pi bits. Pi goods. l = r`, closed, by a case tree on the `nv` bits; `lr` gives the two sides.
fn by_cases(nv: usize, lr: &dyn Fn(&[T]) -> (T, T)) -> T {
    fn go(i: usize, nv: usize, lits: &[T], lr: &dyn Fn(&[T]) -> (T, T)) -> T {
        if i == nv {
            return rfl(lr(lits).0);
        }
        let with = |c: T, rest: bool| -> Vec<T> {
            let tail = (i + 1..nv).filter(|_| rest).map(|j| v(CB[j]));
            lits.iter().cloned().chain([c]).chain(tail).collect()
        };
        let (a, c) = lr(&with(v("$c"), true));
        let motive = lm("$c", bool0(), eqb(a, c));
        ap3(v(CG[i]), motive, go(i + 1, nv, &with(tt(), false), lr), go(i + 1, nv, &with(ff(), false), lr))
    }
    let goods = (0..nv).rev().fold(go(0, nv, &[], lr), |t, i| lm(CG[i], ap(goodbool(), v(CB[i])), t));
    K(ex(&(0..nv).rev().fold(goods, |t, i| lm(CB[i], bool0(), t))))
}
fn conj(ts: &[T]) -> T {
    match ts {
        [a] => a.clone(),
        [a, rest @ ..] => Sig("_c", b(a.clone()), b(conj(rest))),
        [] => panic!("an empty conjunction"),
    }
}
fn pair(ts: &[T], ps: &[T]) -> T {
    match ps {
        [p] => p.clone(),
        [p, rest @ ..] => Pair("_c", b(conj(&ts[1..])), b(p.clone()), b(pair(&ts[1..], rest))),
        [] => panic!("an empty conjunction"),
    }
}
/// Every component of a proof of `conj(ts)`.
fn projections(ts: &[T], t: T) -> Vec<T> {
    let [a, rest @ ..] = ts else { panic!("an empty conjunction") };
    if rest.is_empty() {
        return vec![t];
    }
    let (whole, tail) = (conj(ts), conj(rest));
    let take = |res: T, pick: &'static str| SigRec(b(lm("_r", whole.clone(), res)), b(lm("$l", a.clone(), lm("$r", tail.clone(), v(pick)))), b(t.clone()));
    let mut out = vec![take(a.clone(), "$l")];
    out.extend(projections(rest, take(tail.clone(), "$r")));
    out
}
/// `f ls = f rs` from `ls[q] = rs[q]`.
fn cong(f: &dyn Fn(&[T]) -> T, ls: &[T], rs: &[T], ps: &[T]) -> T {
    let rhs = f(rs);
    (0..ls.len()).fold(rfl(rhs.clone()), |h, q| {
        let at = |c: T| -> Vec<T> { ls[..q].iter().cloned().chain([c]).chain(rs[q + 1..].iter().cloned()).collect() };
        rew(bool0(), ls[q].clone(), rs[q].clone(), ps[q].clone(), lm("t", bool0(), eqb(f(&at(v("t"))), rhs.clone())), h)
    })
}

// ---------- the law ----------
struct Law {
    k: usize,
    sides: [Side; 2],
    enc: Encoding,
}
impl Law {
    fn new(k: usize, t1: &Term, t2: &Term) -> Option<Law> {
        let x: Vec<T> = (0..k).map(|i| v(XS[i])).collect();
        let sides = [side(t1, &x), side(t2, &x)];
        let enc = moore_encoding(&sides[0].m, &sides[1].m, k)?;
        Some(Law { k, sides, enc })
    }
    fn m(&self) -> usize {
        self.enc.phi[0].len()
    }
    /// `Pi x.. Pi goods. body`
    fn over(&self, wrap: &dyn Fn(T, &'static str, T) -> T, body: T) -> T {
        let goods = (0..self.k).rev().fold(body, |t, i| wrap(good_stream(v(XS[i])), GS[i], t));
        (0..self.k).rev().fold(goods, |t, i| wrap(bw(), XS[i], t))
    }
    fn closed(&self, body: T) -> T {
        K(ex(&self.over(&|ty, n, t| lm(n, ty, t), body)))
    }
    fn held(&self, lemma: &T) -> T {
        let with_x = (0..self.k).fold(lemma.clone(), |t, i| ap(t, v(XS[i])));
        (0..self.k).fold(with_x, |t, i| ap(t, v(GS[i])))
    }
    fn ops(&self, p: &T) -> Vec<T> {
        (0..self.k).map(|i| ap(v(XS[i]), p.clone())).collect()
    }
    fn at(&self, sd: usize, p: &T) -> Vec<T> {
        self.sides[sd].carries.iter().map(|c| ap(c.clone(), p.clone())).collect()
    }
    fn phi(&self, sd: usize, j: usize, s: &[T]) -> T {
        table(s, &|bits| self.enc.phi[sd][j][index_of(bits)])
    }
    fn g(&self, j: usize, key: &[T]) -> T {
        table(key, &|bits| self.enc.g[j][index_of(bits)])
    }
    fn step(&self, sd: usize, u: &[T], s: &[T]) -> (T, Vec<T>) {
        self.sides[sd].m.step(&Terms, u, s)
    }
    /// `F_j` at bits `vs`: the output (`j = 0`) or the next `phi_(j - 1)`.
    fn f(&self, sd: usize, j: usize, vs: &[T]) -> T {
        let (o, next) = self.step(sd, &vs[..self.k], &vs[self.k..]);
        if j == 0 { o } else { self.phi(sd, j - 1, &next) }
    }
    /// One side's carries are good at every position, each as a closed lemma over the earlier ones.
    fn good_carries(&self, sd: usize) -> Vec<T> {
        let sdr = &self.sides[sd];
        let mut done: Vec<T> = vec![];
        for c in 0..sdr.carries.len() {
            let pred = |mm: T| p_of(selm(mm, &|w| self.step(sd, &self.ops(&fw(&w)), &self.at(sd, &fw(&w))).1[c].clone(), ff()));
            let hj = |w: T| {
                let p = fw(&w);
                let ug: Vec<Good> = (0..self.k).map(|i| Good { e: ap(v(XS[i]), p.clone()), g: ap(v(GS[i]), p.clone()) }).collect();
                let sg: Vec<Good> = self.at(sd, &p).into_iter().enumerate().map(|(d, e)| {
                    // a carry reads only the earlier ones, so a later one's witness is never used
                    let g = match d {
                        _ if d < c => ap(self.held(&done[d]), p.clone()),
                        _ if d == c => ap(v("$ih"), w.clone()),
                        _ => ff(),
                    };
                    Good { e, g }
                }).collect();
                ap3(sdr.m.step(&Goods, &ug, &sg).1[c].g.clone(), v("$P"), v("$ht"), v("$hf"))
            };
            let motive = |n: T| ap(goodbool(), ap(sdr.carries[c].clone(), n));
            let body = lm("n", nw(), ind(&motive, v("n"), &good_lams, &pred, &hj, v("$hf")));
            done.push(self.closed(body));
        }
        done
    }
    /// `F_j` of a side equals `G_j` of the operand bits and the side's phi, by cases on `k + c` bits.
    fn lemma(&self, sd: usize, j: usize) -> T {
        by_cases(self.k + self.sides[sd].carries.len(), &|vs| {
            let (u, s) = vs.split_at(self.k);
            let key: Vec<T> = u.iter().cloned().chain((0..self.m()).map(|q| self.phi(sd, q, s))).collect();
            (self.f(sd, j, vs), self.g(j, &key))
        })
    }
    fn agree(&self, p: &T) -> Vec<T> {
        (0..self.m()).map(|q| eqb(self.phi(0, q, &self.at(0, p)), self.phi(1, q, &self.at(1, p)))).collect()
    }
    /// With a root `lt`: the last carries agree at `p`, each being the function `dec` of its side's phi.
    fn last_carry(&self, goods: &[Vec<T>; 2], p: &T, ip: &[T]) -> T {
        let m = self.m();
        let mut dec = vec![false; 1 << m];
        for sd in 0..2 {
            for s in 0..1usize << self.sides[sd].carries.len() {
                dec[index_of(&(0..m).map(|j| self.enc.phi[sd][j][s]).collect::<Vec<_>>())] = s & 1 == 1;
            }
        }
        let d = |ph: &[T]| table(ph, &|bits| dec[index_of(bits)]);
        let phis = |sd: usize, s: &[T]| -> Vec<T> { (0..m).map(|q| self.phi(sd, q, s)).collect() };
        let inst = |sd: usize| {
            let lemma = by_cases(self.sides[sd].carries.len(), &|s| (s.last().expect("a borrow").clone(), d(&phis(sd, s))));
            let bits = self.at(sd, p).into_iter().fold(lemma, ap);
            goods[sd].iter().map(|l| ap(self.held(l), p.clone())).fold(bits, ap)
        };
        let (s0, s1) = (self.at(0, p), self.at(1, p));
        let (pl, pr) = (phis(0, &s0), phis(1, &s1));
        let (cl, cr) = (s0.last().expect("a borrow").clone(), s1.last().expect("a borrow").clone());
        let (dl, dr) = (d(&pl), d(&pr));
        let back = sym(cr.clone(), dr.clone(), inst(1));
        trans(cl, dl.clone(), cr.clone(), inst(0), trans(dl, dr, cr, cong(&d, &pl, &pr, ip), back))
    }
    /// The proof of the whole law, and its statement.
    fn proof(&self) -> (T, T) {
        let m = self.m();
        let goods = [self.good_carries(0), self.good_carries(1)];
        let last = self.sides[0].m.last();
        // with a root `lt`, `F_0` is never read: the law is about the last carry
        let lemmas: Vec<Vec<T>> = (0..2).map(|sd| (0..=m).map(|j| if last && j == 0 { ff() } else { self.lemma(sd, j) }).collect()).collect();
        // `F_j` of the left at `p` equals the right's, from the phi agreement `ip` at `p`
        let eq = |j: usize, p: &T, ip: &[T]| {
            let u = self.ops(p);
            let vs = |sd: usize| -> Vec<T> { u.iter().cloned().chain(self.at(sd, p)).collect() };
            let phis = |sd: usize| -> Vec<T> { (0..m).map(|q| self.phi(sd, q, &self.at(sd, p))).collect() };
            let key = |ph: &[T]| -> Vec<T> { u.iter().chain(ph).cloned().collect() };
            let (pl, pr) = (phis(0), phis(1));
            let (fl, fr, gl, gr) = (self.f(0, j, &vs(0)), self.f(1, j, &vs(1)), self.g(j, &key(&pl)), self.g(j, &key(&pr)));
            let inst = |sd: usize| {
                let bits = vs(sd).into_iter().fold(lemmas[sd][j].clone(), ap);
                let ops = (0..self.k).map(|i| ap(v(GS[i]), p.clone()));
                let carries = goods[sd].iter().map(|l| ap(self.held(l), p.clone()));
                ops.chain(carries).fold(bits, ap)
            };
            let link = cong(&|ph| self.g(j, &key(ph)), &pl, &pr, ip);
            let back = sym(fr.clone(), gr.clone(), inst(1));
            trans(fl, gl.clone(), fr.clone(), inst(0), trans(gl, gr, fr, link, back))
        };
        let next = |sd: usize, w: &T| self.step(sd, &self.ops(&fw(w)), &self.at(sd, &fw(w))).1;
        let reduced = |mm: T, sd: usize| -> Vec<T> {
            (0..self.sides[sd].carries.len()).map(|d| selm(mm.clone(), &|w| next(sd, &w)[d].clone(), ff())).collect()
        };
        let pred = |mm: T| {
            let (l, r) = (reduced(mm.clone(), 0), reduced(mm, 1));
            conj(&(0..m).map(|q| eqb(self.phi(0, q, &l), self.phi(1, q, &r))).collect::<Vec<_>>())
        };
        let hj = |w: T| {
            let p = fw(&w);
            let ip = projections(&self.agree(&p), ap(v("$ih"), w.clone()));
            let ts: Vec<T> = (0..m).map(|q| eqb(self.phi(0, q, &next(0, &w)), self.phi(1, q, &next(1, &w)))).collect();
            pair(&ts, &(0..m).map(|q| eq(1 + q, &p, &ip)).collect::<Vec<_>>())
        };
        let start = |sd: usize| vec![ff(); self.sides[sd].carries.len()];
        let ts0: Vec<T> = (0..m).map(|q| eqb(self.phi(0, q, &start(0)), self.phi(1, q, &start(1)))).collect();
        let hn = pair(&ts0, &(0..m).map(|q| rfl(self.phi(0, q, &start(0)))).collect::<Vec<_>>());
        let inv = ind(&|n| conj(&self.agree(&n)), v("n"), &|t| t, &pred, &hj, hn);
        let inv = self.closed(lm("n", nw(), inv));
        let i = v("i");
        let ip = projections(&self.agree(&i), ap(self.held(&inv), i.clone()));
        let whole = if last { self.last_carry(&goods, &i, &ip) } else { eq(0, &i, &ip) };
        let proof = self.over(&|ty, n, t| lm(n, ty, t), lm("i", nw(), whole));
        let stmt = eqb(ap(self.sides[0].root.clone(), i.clone()), ap(self.sides[1].root.clone(), i));
        (proof, self.over(&|ty, n, t| pi_(n, ty, t), pi_("i", nw(), stmt)))
    }
}

fn op2(o: usize) -> impl Fn(Term, Term) -> Term {
    move |a, c| Term::op(o, a, c)
}
fn shl_t(a: Term) -> Term {
    Term::op(SHL1, a, Term::ZERO)
}
fn proved(k: usize, l: Term, r: Term) {
    let name = format!("{} = {}", l.show(), r.show());
    let law = Law::new(k, &l, &r).unwrap_or_else(|| panic!("{name}: no encoding"));
    let (proof, stmt) = law.proof();
    run(&name, &stmt, &proof).map_err(|e| e.chars().take(900).collect::<String>()).unwrap();
}

/// The statement is about `wnat.rs#add` itself, and a proof proves only its own law.
#[test]
fn w_fold_add_associates() {
    let (x, y, z, add) = (Term::v(0), Term::v(1), Term::v(2), op2(ADD));
    let law = Law::new(3, &add(add(x, y), z), &add(x, add(y, z))).unwrap();
    let (proof, stmt) = law.proof();
    run("(x + y) + z = x + (y + z)", &stmt, &proof).unwrap();
    let (a, c, d, i) = (v("x0"), v("x1"), v("x2"), v("i"));
    let by_hand = |r: T| law.over(&|ty, n, t| pi_(n, ty, t), pi_("i", nw(), eqb(ap(add_w(add_w(a.clone(), c.clone()), d.clone()), i.clone()), ap(r, i.clone()))));
    assert!(tatic_kernel::def_eq(&ex(&stmt), &ex(&by_hand(add_w(a.clone(), add_w(c.clone(), d.clone()))))), "not the law as written");
    assert!(run("control: (x + y) + z = x + (y + y)", &by_hand(add_w(a.clone(), add_w(c.clone(), c.clone()))), &proof).is_err());
}
#[test]
fn w_fold_a_false_table_is_rejected() {
    let (x, y, z, add) = (Term::v(0), Term::v(1), Term::v(2), op2(ADD));
    let mut law = Law::new(3, &add(add(x, y), z), &add(x, add(y, z))).unwrap();
    law.enc.g[1][0] = !law.enc.g[1][0];
    let (proof, stmt) = law.proof();
    assert!(run("control: a flipped table bit", &stmt, &proof).is_err());
    assert!(Law::new(2, &add(x, y), &x).is_none(), "a false law has no encoding");
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
/// A theorem's hypotheses hold of real streams: at constant ones and zeros it gives bit 2 of `(7 + 7) + 0`.
#[test]
fn w_fold_a_theorem_applies_to_good_streams() {
    let (x, y, z, add) = (Term::v(0), Term::v(1), Term::v(2), op2(ADD));
    let (proof, _) = Law::new(3, &add(add(x, y), z), &add(x, add(y, z))).unwrap().proof();
    let good = |b: bool| lm("$i", nw(), Goods.konst(b).g);
    let at = [ones(), ones(), zw(), good(true), good(true), good(false), num(2)].into_iter().fold(proof, ap);
    let check = |b: T| tatic_kernel::check(&tatic_kernel::Ctx::new(), &ex(&at), &ex(&eqb(b.clone(), b)));
    check(tt()).unwrap();
    assert!(check(ff()).is_err(), "the wrong bit passed");
}
/// A comparison that varies: its proof proves only its own law, and swapped operands have no encoding.
#[test]
fn w_fold_a_comparison_is_its_own_law() {
    let (x, y, lt, xor) = (Term::v(0), Term::v(1), op2(LT), op2(XOR));
    let law = Law::new(2, &lt(x, y), &lt(xor(y, Term::ONES), xor(x, Term::ONES))).unwrap();
    let (proof, stmt) = law.proof();
    run("x < y = ~y < ~x", &stmt, &proof).unwrap();
    let swapped = side(&lt(y, x), &[v("x0"), v("x1")]).root;
    let wrong = law.over(&|ty, n, t| pi_(n, ty, t), pi_("i", nw(), eqb(ap(law.sides[0].root.clone(), v("i")), ap(swapped, v("i")))));
    assert!(run("control: x < y = y < x", &wrong, &proof).is_err());
    assert!(Law::new(2, &lt(x, y), &lt(y, x)).is_none(), "a false comparison has no encoding");
}
/// `lt` is a result, not a stream: below the root `Machine::step` would read it as `sub`, and a root `lt` is no word.
#[test]
fn w_fold_lt_outside_the_root_has_no_law() {
    let (x, y, z, add, sub, lt) = (Term::v(0), Term::v(1), Term::v(2), op2(ADD), op2(SUB), op2(LT));
    assert!(Law::new(3, &add(lt(x, y), z), &add(sub(x, y), z)).is_none(), "lt read as sub");
    assert!(Law::new(3, &add(lt(x, y), z), &add(z, lt(x, y))).is_none(), "lt below the root");
    assert!(Law::new(3, &lt(lt(x, y), z), &lt(lt(x, y), z)).is_none(), "lt under a root lt");
    assert!(Law::new(1, &lt(x, x), &Term::ZERO).is_none(), "a root lt against a word");
}
/// A law says only what its streams compute: at closed operands they give the words, and a root `lt` at `p` compares the low `p` bits.
#[test]
fn w_fold_streams_compute_the_words() {
    let nb = 3;
    let (x, y, add, sub) = (Term::v(0), Term::v(1), op2(ADD), op2(SUB));
    let terms = [add(x, y), sub(x, y), op2(AND)(x, y), op2(OR)(x, y), op2(XOR)(x, y), shl_t(x), sub(add(x, x), shl_t(y)), Term::ONES];
    for (a, c) in [(5u128, 3u128), (7, 7), (6, 1), (0, 5), (2, 6)] {
        let s = [stream_of(a, nb), stream_of(c, nb)];
        for t in &terms {
            let root = side(t, &s).root;
            for p in 0..nb {
                let want = bit_of(t.interp(nb, &[a, c]), p);
                assert!(tatic_kernel::def_eq(&ex(&ap(root.clone(), num(p))), &ex(&want)), "{}: {a} {c} bit {p}", t.show());
            }
        }
        let root = side(&op2(LT)(x, y), &s).root;
        for p in 0..=nb {
            let low = (1u128 << p) - 1;
            assert!(tatic_kernel::def_eq(&ex(&ap(root.clone(), num(p))), &ex(&Terms.konst(a & low < c & low))), "lt {a} {c} at {p}");
        }
    }
}
/// Equal terms over `x`, `y` and two operator levels, and comparisons of one-level terms, sampled by a stride: every pair
/// gets an accepted proof, or differs at some other width.
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
    let (mut pairs, mut tried, mut none) = (0usize, 0usize, 0usize);
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
        if pairs % stride != 0 {
            continue;
        }
        let Some(law) = Law::new(2, &t, &r) else {
            // the classes are by width 4 only: a pair with no encoding must differ at another width
            let differ = |n: u32| {
                let m = (1u128 << n) - 1;
                (0..=m).flat_map(|x| (0..=m).map(move |y| (x, y))).find(|(x, y)| t.interp(n as usize, &[*x, *y]) != r.interp(n as usize, &[*x, *y])).map(|w| (n, w))
            };
            let witness = (1..=6).find_map(differ).unwrap_or_else(|| panic!("{} = {}: no encoding, yet equal at widths 1 to 6", t.show(), r.show()));
            println!("no encoding: {} = {}, differ at {witness:?}", t.show(), r.show());
            none += 1;
            continue;
        };
        tried += 1;
        let (proof, stmt) = law.proof();
        tatic_kernel::check(&tatic_kernel::Ctx::new(), &ex(&proof), &ex(&stmt))
            .unwrap_or_else(|e| panic!("{} = {}: {}", t.show(), r.show(), e.chars().take(500).collect::<String>()));
    }
    println!("pairs={pairs} stride={stride} tried={tried} no-encoding={none}");
    assert!(tried > 0);
}
