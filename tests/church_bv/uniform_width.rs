// Spike kept as a test (2026-11-01; finding in docs/tier-cycle.md, "Laws uniform in the width"): can the unchanged kernel check laws that are uniform in
// the bit width, using "bits as a stream with prefix statements" (part2 spec, section 53, option 3)?
//
// Level facts that shape the design (kernel has no cumulativity; Pi lands in max(dom, cod); Church X over
// Sort k lives in Sort k+1):
//   Bool0 = Pi C:Sort0. C->C->C            : Sort1
//   Nat0  = Pi C:Sort0. C->(C->C)->C       : Sort1   (index type of the INPUT streams)
//   Nat1  = Pi C:Sort1. C->(C->C)->C       : Sort2   (iteration count; can fold into Sort1 state)
//   Bits  = Nat0 -> Bool0                  : Sort1
// A carry stream "by Church-Nat recursion" needs the step to know the position i, so the state must carry i
// (or the streams).  With ONE Nat that is a predicativity wall (the state would mention Nat itself).  Escape
// used here: two Church Nats.  The fold runs over Nat1 into the Sort1 state S = Sigma(_:Nat0).Bool0
// (position-as-Nat0 numeral, carry); the input streams are indexed by Nat0; the fold re-builds the Nat0 numeral
// of its own count as it goes.  The output stream `add x y` is indexed by Nat1 (bit N of the sum), and
// `embed N := N Nat0 zero0 succ0` gives the Nat0 numeral to read the input stream at that position.
// `Good1 N` is the induction witness over Nat1 with motives in Sort1 (so `Id` statements fit).
//
// Statements are POINTWISE in the position N (a causal bit-serial adder: bit N depends only on bits <= N):
//   Pi N. Good1 N -> Pi x. (Pi i. GoodBool (x i)) -> Id(Bool, add x zero N, x (embed N))
// which says the first-n-bits law for every n at once (prefix_equal n f g := Pi N. LE N n -> Id(f N, g N) follows
// by dropping the LE hypothesis; see `prefix_corollary` below).  Pointwise is the induction-friendly form: the
// induction is on the position N itself, no extra `below` relation inside the step.
use std::time::Instant;
use tatic::kernel::{self, Ctx, Expr};

#[derive(Clone)]
enum T {
    V(&'static str),
    S(u32),
    Pi(&'static str, Box<T>, Box<T>),
    Lm(&'static str, Box<T>, Box<T>),
    A(Box<T>, Box<T>),
    Id(Box<T>, Box<T>, Box<T>),
    Refl(Box<T>),
    J(Box<T>, Box<T>, Box<T>, Box<T>, Box<T>),
    Sig(&'static str, Box<T>, Box<T>),
    Pair(&'static str, Box<T>, Box<T>, Box<T>),
    SigRec(Box<T>, Box<T>, Box<T>),
}
use T::*;
fn b(t: T) -> Box<T> {
    Box::new(t)
}
fn v(n: &'static str) -> T {
    V(n)
}
fn s(k: u32) -> T {
    S(k)
}
fn pi_(n: &'static str, a: T, c: T) -> T {
    Pi(n, b(a), b(c))
}
fn lm(n: &'static str, a: T, c: T) -> T {
    Lm(n, b(a), b(c))
}
fn ap(f: T, a: T) -> T {
    A(b(f), b(a))
}
fn ap2(f: T, a: T, c: T) -> T {
    ap(ap(f, a), c)
}
fn ap3(f: T, a: T, c: T, d: T) -> T {
    ap(ap2(f, a, c), d)
}
fn idt(a: T, x: T, y: T) -> T {
    Id(b(a), b(x), b(y))
}
fn rfl(a: T) -> T {
    Refl(b(a))
}
fn arr(a: T, c: T) -> T {
    pi_("_", a, c)
}

fn comp(t: &T, env: &mut Vec<&'static str>) -> Expr {
    match t {
        V(n) => {
            let i = env.iter().rposition(|x| x == n).unwrap_or_else(|| panic!("unbound {n}"));
            kernel::var((env.len() - 1 - i) as u32)
        }
        S(k) => kernel::sort(*k),
        Pi(n, a, c) | Lm(n, a, c) | Sig(n, a, c) => {
            let ea = comp(a, env);
            env.push(n);
            let ec = comp(c, env);
            env.pop();
            match t {
                Pi(..) => kernel::pi(ea, ec),
                Lm(..) => kernel::lam(ea, ec),
                _ => kernel::sigma(ea, ec),
            }
        }
        A(f, a) => {
            let (ef, ea) = (comp(f, env), comp(a, env));
            kernel::app(ef, ea)
        }
        Id(a, x, y) => {
            let (ea, ex, ey) = (comp(a, env), comp(x, env), comp(y, env));
            kernel::id(ea, ex, ey)
        }
        Refl(a) => kernel::refl(comp(a, env)),
        J(m, bs, a, c, p) => {
            let (em, eb, ea, ec, ep) = (comp(m, env), comp(bs, env), comp(a, env), comp(c, env), comp(p, env));
            kernel::jelim(em, eb, ea, ec, ep)
        }
        Pair(n, fam, a, c) => {
            env.push(n);
            let ef = comp(fam, env);
            env.pop();
            let (ea, ec) = (comp(a, env), comp(c, env));
            kernel::pair(ef, ea, ec)
        }
        SigRec(m, st, tg) => {
            let (em, es, et) = (comp(m, env), comp(st, env), comp(tg, env));
            kernel::sigrec(em, es, et)
        }
    }
}
fn ex(t: &T) -> Expr {
    comp(t, &mut vec![])
}

// ---------- Church Bool / Nat ----------
fn bool0() -> T {
    pi_("C", s(0), arr(v("C"), arr(v("C"), v("C"))))
}
fn tt() -> T {
    lm("C", s(0), lm("t", v("C"), lm("f", v("C"), v("t"))))
}
fn ff() -> T {
    lm("C", s(0), lm("t", v("C"), lm("f", v("C"), v("f"))))
}
fn bool2(body: T) -> T {
    lm("a", bool0(), lm("b", bool0(), lm("C", s(0), lm("t", v("C"), lm("f", v("C"), body)))))
}
fn and_() -> T {
    bool2(ap2(ap(v("a"), v("C")), ap3(v("b"), v("C"), v("t"), v("f")), v("f")))
}
fn or_() -> T {
    bool2(ap3(v("a"), v("C"), v("t"), ap3(v("b"), v("C"), v("t"), v("f"))))
}
fn xor_() -> T {
    bool2(ap3(v("a"), v("C"), ap3(v("b"), v("C"), v("f"), v("t")), ap3(v("b"), v("C"), v("t"), v("f"))))
}
fn maj(a: T, c: T, d: T) -> T {
    ap2(or_(), ap2(and_(), a.clone(), c.clone()), ap2(and_(), d, ap2(or_(), a, c)))
}
fn xor(a: T, c: T) -> T {
    ap2(xor_(), a, c)
}
fn nat(k: u32) -> T {
    pi_("C", s(k), pi_("z", v("C"), pi_("s", arr(v("C"), v("C")), v("C"))))
}
fn zero(k: u32) -> T {
    lm("C", s(k), lm("z", v("C"), lm("s", arr(v("C"), v("C")), v("z"))))
}
fn succ(k: u32) -> T {
    lm("n", nat(k), lm("C", s(k), lm("z", v("C"), lm("s", arr(v("C"), v("C")),
        ap(v("s"), ap3(v("n"), v("C"), v("z"), v("s")))))))
}
fn goodbool() -> T {
    lm("a", bool0(), pi_("P", arr(bool0(), s(1)), arr(ap(v("P"), tt()), arr(ap(v("P"), ff()), ap(v("P"), v("a"))))))
}
fn good1(k: u32) -> T {
    lm("n", nat(k + 1), pi_("P", arr(nat(k + 1), s(k + 1)), arr(ap(v("P"), zero(k + 1)),
        arr(pi_("m", nat(k + 1), arr(ap(v("P"), v("m")), ap(v("P"), ap(succ(k + 1), v("m"))))), ap(v("P"), v("n"))))))
}

// ---------- streams, state, bit-serial adder ----------
fn bits(k: u32) -> T {
    arr(nat(k), bool0())
}
fn zs(k: u32) -> T {
    lm("i", nat(k), ff())
}
fn state(k: u32) -> T {
    Sig("_s", b(nat(k)), b(bool0()))
}
fn pair_s(k: u32, a: T, c: T) -> T {
    Pair("_k", b(bool0()), b(a), b(c))
}
fn fst(k: u32, u: T) -> T {
    SigRec(b(lm("_s", state(k), nat(k))), b(lm("a", nat(k), lm("b", bool0(), v("a")))), b(u))
}
fn snd(k: u32, u: T) -> T {
    SigRec(b(lm("_s", state(k), bool0())), b(lm("a", nat(k), lm("b", bool0(), v("b")))), b(u))
}
/// one step of the carry machine: (i, c) -> (i+1, maj(x i, y i, c))
fn step(k: u32, x: T, y: T) -> T {
    lm("u", state(k), pair_s(k, ap(succ(k), fst(k, v("u"))),
        maj(ap(x, fst(k, v("u"))), ap(y, fst(k, v("u"))), snd(k, v("u")))))
}
/// the fold over the Nat1 count n: (zero0, false) --step^n-->
fn st(k: u32, x: T, y: T, n: T) -> T {
    ap3(n, state(k), pair_s(k, zero(k), ff()), step(k, x, y))
}
/// sum bit at the state's position: x_i xor y_i xor carry_i
fn sumfn(k: u32, x: T, y: T, u: T) -> T {
    xor(xor(ap(x, fst(k, u.clone())), ap(y, fst(k, u.clone()))), snd(k, u))
}
fn sumbit(k: u32, x: T, y: T, n: T) -> T {
    sumfn(k, x.clone(), y.clone(), st(k, x, y, n))
}
fn embed(k: u32, n: T) -> T {
    ap3(n, nat(k), zero(k), succ(k))
}

// ---------- J helpers ----------
/// rew(A, l, r, p : l = r, fam, h : fam r) : fam l
fn rew(a: T, l: T, r: T, p: T, fam: T, h: T) -> T {
    let motive = lm("$l", a.clone(), lm("$r", a.clone(), lm("$q", idt(a.clone(), v("$l"), v("$r")),
        pi_("$h", ap(fam.clone(), v("$r")), ap(fam.clone(), v("$l"))))));
    let base = lm("$x", a.clone(), lm("$h", ap(fam, v("$x")), v("$h")));
    ap(J(b(motive), b(base), b(l), b(r), b(p)), h)
}
/// case split on a symbolic bit with witness ga: F(b) = G(b) for b in {true,false}, by refl
fn cases1(ga: T, f: &dyn Fn(T) -> T, g: &dyn Fn(T) -> T) -> T {
    let motive = lm("$b", bool0(), idt(bool0(), f(v("$b")), g(v("$b"))));
    ap3(ga, motive, rfl(f(tt())), rfl(f(ff())))
}
/// two bits: L(a,b) = R(a,b) in type ty; yb is the actual second bit (witness gb)
fn cases2(ga: T, gb: T, yb: T, ty: T, l: &dyn Fn(T, T) -> T, r: &dyn Fn(T, T) -> T) -> T {
    let tm = |a: T, c: T| idt(ty.clone(), l(a.clone(), c.clone()), r(a, c));
    let m1 = lm("$a", bool0(), tm(v("$a"), yb));
    let inner = |av: T| {
        let m2 = lm("$b", bool0(), tm(av.clone(), v("$b")));
        ap3(gb.clone(), m2, rfl(l(av.clone(), tt())), rfl(l(av, ff())))
    };
    ap3(ga, m1, inner(tt()), inner(ff()))
}

// ---------- (b) add x zero = x ----------
/// with_y = false: y is the zero stream (the law). with_y = true: y is a symbolic stream (the false law
/// `add x y = x`, used as a negative control with the very same proof skeleton).
fn stmt_b(k: u32, with_y: bool) -> T {
    let y = if with_y { v("y") } else { zs(k) };
    let body = idt(bool0(), sumbit(k, v("x"), y, v("N")), ap(v("x"), embed(k, v("N"))));
    let body = if with_y {
        pi_("y", bits(k), arr(pi_("i", nat(k), ap(goodbool(), ap(v("y"), v("i")))), body))
    } else {
        body
    };
    pi_("N", nat(k + 1), arr(ap(good1(k), v("N")), pi_("x", bits(k),
        arr(pi_("i", nat(k), ap(goodbool(), ap(v("x"), v("i")))), body))))
}
fn proof_b(k: u32, with_y: bool) -> T {
    let y = if with_y { v("y") } else { zs(k) };
    let stx = |m: T| st(k, v("x"), y.clone(), m);
    // one induction on the count: st M = (embed M, false), the position tracks the count and the carry stays false.
    // (Two separate statements, `fst = embed` and `snd = false`, would need an Id on Bool0 in the Good motive's sort,
    // which is Sort(k+1); a state equality lives there for every k.)
    let target = |m: T| pair_s(k, embed(k, m), ff());
    let pm = lm("M", nat(k + 1), idt(state(k), stx(v("M")), target(v("M"))));
    let e = |m: T| embed(k, m);
    let m0 = |m: T| maj(ap(v("x"), e(m.clone())), ap(y.clone(), e(m)), ff());
    // h: Id(state, step (embed m, false), (succ (embed m), false)), from the bit x_m being true or false
    let to_false = cases1(ap(v("gx"), e(v("m"))), &|bb| maj(bb, ff(), ff()), &|_| ff());
    let h = rew(bool0(), m0(v("m")), ff(), to_false,
        lm("t", bool0(), idt(state(k), pair_s(k, ap(succ(k), e(v("m"))), v("t")), pair_s(k, ap(succ(k), e(v("m"))), ff()))),
        rfl(pair_s(k, ap(succ(k), e(v("m"))), ff())));
    let step_ = lm("m", nat(k + 1), lm("ih", idt(state(k), stx(v("m")), target(v("m"))),
        rew(state(k), stx(v("m")), target(v("m")), v("ih"),
            lm("t", state(k), idt(state(k), ap(step(k, v("x"), y.clone()), v("t")), pair_s(k, ap(succ(k), e(v("m"))), ff()))),
            h)));
    let pn = ap3(v("g"), pm, rfl(pair_s(k, zero(k), ff())), step_);
    let en = embed(k, v("N"));
    // per-bit leaf: xor(xor(a,false),false) = a
    let leaf = cases1(ap(v("gx"), en.clone()), &|bb| xor(xor(bb.clone(), ff()), ff()), &|bb| bb);
    let fin = rew(state(k), stx(v("N")), target(v("N")), pn,
        lm("t", state(k), idt(bool0(), sumfn(k, v("x"), y.clone(), v("t")), ap(v("x"), en.clone()))), leaf);
    let core = if with_y { lm("y", bits(k), lm("gy", pi_("i", nat(k), ap(goodbool(), ap(v("y"), v("i")))), fin)) } else { fin };
    lm("N", nat(k + 1), lm("g", ap(good1(k), v("N")), lm("x", bits(k),
        lm("gx", pi_("i", nat(k), ap(goodbool(), ap(v("x"), v("i")))), core))))
}

// ---------- (c) add x y = add y x ----------
fn stmt_c(k: u32) -> T {
    let gb = |s_: &'static str| pi_("i", nat(k), ap(goodbool(), ap(v(s_), v("i"))));
    pi_("N", nat(k + 1), arr(ap(good1(k), v("N")), pi_("x", bits(k), pi_("y", bits(k), arr(gb("x"), arr(gb("y"),
        idt(bool0(), sumbit(k, v("x"), v("y"), v("N")), sumbit(k, v("y"), v("x"), v("N")))))))))
}
fn proof_c(k: u32) -> T {
    let gb = |s_: &'static str| pi_("i", nat(k), ap(goodbool(), ap(v(s_), v("i"))));
    let xy = |m: T| st(k, v("x"), v("y"), m);
    let yx = |m: T| st(k, v("y"), v("x"), m);
    let pm = lm("M", nat(k + 1), idt(state(k), xy(v("M")), yx(v("M"))));
    let r = yx(v("m"));
    let leaf = cases2(
        ap(v("gx"), fst(k, r.clone())), ap(v("gy"), fst(k, r.clone())), ap(v("y"), fst(k, r.clone())), state(k),
        &|a, c| pair_s(k, ap(succ(k), fst(k, r.clone())), maj(a, c, snd(k, r.clone()))),
        &|a, c| pair_s(k, ap(succ(k), fst(k, r.clone())), maj(c, a, snd(k, r.clone()))),
    );
    let stepc = lm("m", nat(k + 1), lm("ih", idt(state(k), xy(v("m")), yx(v("m"))),
        rew(state(k), xy(v("m")), yx(v("m")), v("ih"),
            lm("t", state(k), idt(state(k), ap(step(k, v("x"), v("y")), v("t")), ap(step(k, v("y"), v("x")), yx(v("m"))))),
            leaf)));
    let pn = ap3(v("g"), pm, rfl(pair_s(k, zero(k), ff())), stepc);
    let r2 = yx(v("N"));
    let leaf2 = cases2(
        ap(v("gx"), fst(k, r2.clone())), ap(v("gy"), fst(k, r2.clone())), ap(v("y"), fst(k, r2.clone())), bool0(),
        &|a, c| xor(xor(a, c), snd(k, r2.clone())),
        &|a, c| xor(xor(c, a), snd(k, r2.clone())),
    );
    let fin = rew(state(k), xy(v("N")), r2.clone(), pn,
        lm("t", state(k), idt(bool0(), sumfn(k, v("x"), v("y"), v("t")), sumfn(k, v("y"), v("x"), r2))), leaf2);
    lm("N", nat(k + 1), lm("g", ap(good1(k), v("N")), lm("x", bits(k), lm("y", bits(k),
        lm("gx", gb("x"), lm("gy", gb("y"), fin))))))
}

fn run(name: &str, stmt: &T, proof: &T) -> Result<(), String> {
    let (ty, pf) = (ex(stmt), ex(proof));
    let t0 = Instant::now();
    let r = kernel::check(&Ctx::new(), &pf, &ty);
    let dt = t0.elapsed();
    match &r {
        Ok(()) => println!("[{name}] ACCEPTED in {:.1} ms", dt.as_secs_f64() * 1e3),
        Err(m) => println!("[{name}] REJECTED in {:.1} ms: {m}", dt.as_secs_f64() * 1e3),
    }
    r
}

#[test]
fn well_formedness_of_the_building_blocks() {
    let k = 0;
    for (n, t) in [("bool0", bool0()), ("nat0", nat(k)), ("nat1", nat(k + 1)), ("bits", bits(k)), ("state", state(k)),
        ("goodbool", goodbool()), ("good1", good1(k)), ("step", step(k, v("x"), v("y")))] {
        let _ = n;
        let _ = t;
    }
    // closed pieces
    for (n, t) in [("bool0", bool0()), ("nat1", nat(k + 1)), ("bits", bits(k)), ("state", state(k)), ("good1", good1(k))] {
        if let Err(m) = kernel::typecheck(&ex(&t)) {
            panic!("{n}: {m}");
        }
    }
}

#[test]
fn b_add_zero_uniform() {
    let k = 0;
    run("b: add x 0 = x, Pi N. Good1 N -> ...", &stmt_b(k, false), &proof_b(k, false)).unwrap();
}

#[test]
fn c_add_comm_uniform() {
    let k = 0;
    run("c: add x y = add y x, Pi N. Good1 N -> ...", &stmt_c(k), &proof_c(k)).unwrap();
}

#[test]
fn d_negative_controls() {
    let k = 0;
    // (1) the proof skeleton of (b) against the false law add x y = x (y symbolic)
    assert!(run("d1: add x y = x (b-skeleton)", &stmt_b(k, true), &proof_b(k, true)).is_err());
    // (2) a false per-bit leaf: xor(xor(a,false),false) = false
    let a_ty = pi_("a", bool0(), arr(ap(goodbool(), v("a")), idt(bool0(), xor(xor(v("a"), ff()), ff()), ff())));
    let a_pf = lm("a", bool0(), lm("ga", ap(goodbool(), v("a")),
        cases1(v("ga"), &|bb| xor(xor(bb, ff()), ff()), &|_| ff())));
    assert!(run("d2: false leaf", &a_ty, &a_pf).is_err());
    // (3) a false law in the same family: the sum bit equals the CARRY-free xor, i.e. add x y = x xor y.
    //     Stated as sumbit = x xor y, with the c-skeleton's leaf (cannot hold: carries differ).
    let bad = pi_("N", nat(k + 1), arr(ap(good1(k), v("N")), pi_("x", bits(k), pi_("y", bits(k),
        idt(bool0(), sumbit(k, v("x"), v("y"), v("N")), xor(ap(v("x"), embed(k, v("N"))), ap(v("y"), embed(k, v("N")))))))));
    // no proof attempt can pass; use the (c) proof as the (wrong-typed) candidate
    assert!(run("d3: add x y = x xor y vs c-proof", &bad, &proof_c(k)).is_err());
}

#[test]
fn prefix_corollary() {
    let k = 0;
    // prefix_equal n f g := Pi N. Good1 N -> LE N n -> Id(f N, g N)  with  LE N n := Pi P:(Nat1->Sort1). P N -> (Pi m. P m -> P (succ m)) -> P n
    let le = |a: T, c: T| pi_("P", arr(nat(k + 1), s(1)), arr(ap(v("P"), a),
        arr(pi_("m", nat(k + 1), arr(ap(v("P"), v("m")), ap(v("P"), ap(succ(k + 1), v("m"))))), ap(v("P"), c))));
    let xzero = |n: T| idt(bool0(), sumbit(k, v("x"), zs(k), n.clone()), ap(v("x"), embed(k, n)));
    let stmt = pi_("n", nat(k + 1), arr(ap(good1(k), v("n")), pi_("x", bits(k),
        arr(pi_("i", nat(k), ap(goodbool(), ap(v("x"), v("i")))),
            pi_("N", nat(k + 1), arr(ap(good1(k), v("N")), arr(le(v("N"), v("n")), xzero(v("N")))))))));
    // proof: ignore n, g, LE; use the pointwise theorem
    let pf = lm("n", nat(k + 1), lm("gn", ap(good1(k), v("n")), lm("x", bits(k),
        lm("gx", pi_("i", nat(k), ap(goodbool(), ap(v("x"), v("i")))),
            lm("N", nat(k + 1), lm("g", ap(good1(k), v("N")), lm("hle", le(v("N"), v("n")),
                ap3(proof_b(k, false), v("N"), v("g"), v("x")).clone()
                    .pipe(|t| ap(t, v("gx"))))))))));
    run("prefix corollary", &stmt, &pf).unwrap();
}

trait Pipe: Sized {
    fn pipe<R>(self, f: impl FnOnce(Self) -> R) -> R {
        f(self)
    }
}
impl Pipe for T {}

#[test]
fn e_sanity_adder_computes_and_more_controls() {
    let k = 0;
    let num1 = |m: u32| {
        let mut e = zero(k + 1);
        for _ in 0..m {
            e = ap(succ(k + 1), e);
        }
        e
    };
    let ones = lm("i", nat(k), tt());
    // all-ones + all-ones: bit0 = 0, then carry 1 forever (bits 0,1,1,1)
    let want = [ff(), tt(), tt(), tt()];
    for (m, w) in want.iter().enumerate() {
        let lhs = ex(&sumbit(k, ones.clone(), ones.clone(), num1(m as u32)));
        assert!(kernel::def_eq(&lhs, &ex(w)), "bit {m} of ones+ones");
    }
    // all-ones + zero = all ones; zero + zero = zero
    assert!(kernel::def_eq(&ex(&sumbit(k, ones.clone(), zs(k), num1(5))), &ex(&tt())));
    assert!(kernel::def_eq(&ex(&sumbit(k, zs(k), zs(k), num1(5))), &ex(&ff())));
    // (b) with the right-hand side replaced by `false` must fail with the real proof
    let bad = pi_("N", nat(k + 1), arr(ap(good1(k), v("N")), pi_("x", bits(k),
        arr(pi_("i", nat(k), ap(goodbool(), ap(v("x"), v("i")))),
            idt(bool0(), sumbit(k, v("x"), zs(k), v("N")), ff())))));
    assert!(run("d4: add x 0 = false", &bad, &proof_b(k, false)).is_err());
    // (c) false variant: add x y = add y y
    let bad2 = pi_("N", nat(k + 1), arr(ap(good1(k), v("N")), pi_("x", bits(k), pi_("y", bits(k),
        arr(pi_("i", nat(k), ap(goodbool(), ap(v("x"), v("i")))), arr(pi_("i", nat(k), ap(goodbool(), ap(v("y"), v("i")))),
            idt(bool0(), sumbit(k, v("x"), v("y"), v("N")), sumbit(k, v("y"), v("y"), v("N")))))))));
    assert!(run("d5: add x y = add y y vs c-proof", &bad2, &proof_c(k)).is_err());
}

// ---------- bridge probe: a stream read off an n-bit tuple ----------
// Nat0 can only eliminate into Sort0 and Bool0 is Sort1, so the lookup indexes by Nat1 (which eliminates into Sort1).
// sx := \i:Nat1. x Bool0 (i (Bool0^n -> Bool0) proj_0 rot), proj_0 a_0..a_(n-1) = a_0 and rot p a_0..a_(n-1) = p a_1..a_(n-1) false,
// so proj_k picks a_k and runs off the end into false.
const AN: [&str; 8] = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"];
fn arrows(n: usize, res: T) -> T {
    (0..n).fold(res, |acc, _| arr(bool0(), acc))
}
fn bvt(n: usize) -> T {
    pi_("C", s(1), arr(arrows(n, v("C")), v("C")))
}
fn tuple(bits: &[T]) -> T {
    lm("C", s(1), lm("k", arrows(bits.len(), v("C")), bits.iter().fold(v("k"), |f, a| ap(f, a.clone()))))
}
fn proj0(n: usize) -> T {
    (0..n).rev().fold(v(AN[0]), |body, i| lm(AN[i], bool0(), body))
}
fn rot(n: usize) -> T {
    let cn = arrows(n, bool0());
    let call = (1..n).fold(v("p"), |f, i| ap(f, v(AN[i])));
    let call = ap(call, ff());
    lm("p", cn, (0..n).rev().fold(call, |body, i| lm(AN[i], bool0(), body)))
}
fn lookup(n: usize) -> T {
    lm("x", bvt(n), lm("i", nat(1), ap2(ap(v("x"), bool0()), ap3(v("i"), arrows(n, bool0()), proj0(n), rot(n)).clone().pipe(|t| t), ff()).pipe(|_| {
        ap(ap(v("x"), bool0()), ap3(v("i"), arrows(n, bool0()), proj0(n), rot(n)))
    })))
}

#[test]
fn bridge_probe_lookup_types_and_reads_the_tuple() {
    let n = 3;
    let ty = ex(&lookup(n));
    kernel::typecheck(&ty).unwrap_or_else(|m| panic!("lookup: {m}"));
    let num1 = |k: u32| (0..k).fold(zero(1), |e, _| ap(succ(1), e));
    let x = tuple(&[tt(), ff(), tt()]);
    for (k, want) in [tt(), ff(), tt(), ff(), ff()].iter().enumerate() {
        let got = ex(&ap2(lookup(n), x.clone(), num1(k as u32)).pipe(|_| ap(ap(lookup(n), x.clone()), num1(k as u32))));
        assert!(kernel::def_eq(&got, &ex(want)), "bit {k}");
    }
}

#[test]
fn b_add_zero_at_higher_levels() {
    for k in [1, 2, 3] {
        run(&format!("b at level {k}"), &stmt_b(k, false), &proof_b(k, false)).unwrap();
    }
}
