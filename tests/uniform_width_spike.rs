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
fn good1() -> T {
    lm("n", nat(1), pi_("P", arr(nat(1), s(1)), arr(ap(v("P"), zero(1)),
        arr(pi_("m", nat(1), arr(ap(v("P"), v("m")), ap(v("P"), ap(succ(1), v("m"))))), ap(v("P"), v("n"))))))
}

// ---------- streams, state, bit-serial adder ----------
fn bits() -> T {
    arr(nat(0), bool0())
}
fn zs() -> T {
    lm("i", nat(0), ff())
}
fn state() -> T {
    Sig("_s", b(nat(0)), b(bool0()))
}
fn pair_s(a: T, c: T) -> T {
    Pair("_k", b(bool0()), b(a), b(c))
}
fn fst(u: T) -> T {
    SigRec(b(lm("_s", state(), nat(0))), b(lm("a", nat(0), lm("b", bool0(), v("a")))), b(u))
}
fn snd(u: T) -> T {
    SigRec(b(lm("_s", state(), bool0())), b(lm("a", nat(0), lm("b", bool0(), v("b")))), b(u))
}
/// one step of the carry machine: (i, c) -> (i+1, maj(x i, y i, c))
fn step(x: T, y: T) -> T {
    lm("u", state(), pair_s(ap(succ(0), fst(v("u"))),
        maj(ap(x, fst(v("u"))), ap(y, fst(v("u"))), snd(v("u")))))
}
/// the fold over the Nat1 count n: (zero0, false) --step^n-->
fn st(x: T, y: T, n: T) -> T {
    ap3(n, state(), pair_s(zero(0), ff()), step(x, y))
}
/// sum bit at the state's position: x_i xor y_i xor carry_i
fn sumfn(x: T, y: T, u: T) -> T {
    xor(xor(ap(x, fst(u.clone())), ap(y, fst(u.clone()))), snd(u))
}
fn sumbit(x: T, y: T, n: T) -> T {
    sumfn(x.clone(), y.clone(), st(x, y, n))
}
fn embed(n: T) -> T {
    ap3(n, nat(0), zero(0), succ(0))
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
fn stmt_b(with_y: bool) -> T {
    let y = if with_y { v("y") } else { zs() };
    let body = idt(bool0(), sumbit(v("x"), y, v("N")), ap(v("x"), embed(v("N"))));
    let body = if with_y {
        pi_("y", bits(), arr(pi_("i", nat(0), ap(goodbool(), ap(v("y"), v("i")))), body))
    } else {
        body
    };
    pi_("N", nat(1), arr(ap(good1(), v("N")), pi_("x", bits(),
        arr(pi_("i", nat(0), ap(goodbool(), ap(v("x"), v("i")))), body))))
}
fn proof_b(with_y: bool) -> T {
    let y = if with_y { v("y") } else { zs() };
    let stx = |m: T| st(v("x"), y.clone(), m);
    // P2 M := snd (st M) = false     (carry stays false)
    let p2m = lm("M", nat(1), idt(bool0(), snd(stx(v("M"))), ff()));
    let step2 = lm("m", nat(1), lm("ih", idt(bool0(), snd(stx(v("m"))), ff()),
        rew(bool0(), snd(stx(v("m"))), ff(), v("ih"),
            lm("t", bool0(), idt(bool0(), maj(ap(v("x"), fst(stx(v("m")))), ff(), v("t")), ff())),
            cases1(ap(v("gx"), fst(stx(v("m")))), &|bb| maj(bb, ff(), ff()), &|_| ff()))));
    let p2 = ap3(v("g"), p2m, rfl(ff()), step2);
    // P1 M := fst (st M) = embed M     (position tracks the count)
    let p1m = lm("M", nat(1), idt(nat(0), fst(stx(v("M"))), embed(v("M"))));
    let step1 = lm("m", nat(1), lm("ih", idt(nat(0), fst(stx(v("m"))), embed(v("m"))),
        rew(nat(0), fst(stx(v("m"))), embed(v("m")), v("ih"),
            lm("t", nat(0), idt(nat(0), ap(succ(0), v("t")), ap(succ(0), embed(v("m"))))),
            rfl(ap(succ(0), embed(v("m")))))));
    let p1 = ap3(v("g"), p1m, rfl(zero(0)), step1);
    let u1 = fst(stx(v("N")));
    let c = snd(stx(v("N")));
    let e = embed(v("N"));
    // per-bit leaf: xor(xor(a,false),false) = a
    let leaf = cases1(ap(v("gx"), e.clone()), &|bb| xor(xor(bb.clone(), ff()), ff()), &|bb| bb);
    let inner = rew(nat(0), u1.clone(), e.clone(), p1,
        lm("t", nat(0), idt(bool0(), xor(xor(ap(v("x"), v("t")), ff()), ff()), ap(v("x"), e.clone()))), leaf);
    let outer = rew(bool0(), c, ff(), p2,
        lm("t", bool0(), idt(bool0(), xor(xor(ap(v("x"), u1), ff()), v("t")), ap(v("x"), e))), inner);
    let core = if with_y { lm("y", bits(), lm("gy", pi_("i", nat(0), ap(goodbool(), ap(v("y"), v("i")))), outer)) } else { outer };
    lm("N", nat(1), lm("g", ap(good1(), v("N")), lm("x", bits(),
        lm("gx", pi_("i", nat(0), ap(goodbool(), ap(v("x"), v("i")))), core))))
}

// ---------- (c) add x y = add y x ----------
fn stmt_c() -> T {
    let gb = |s_: &'static str| pi_("i", nat(0), ap(goodbool(), ap(v(s_), v("i"))));
    pi_("N", nat(1), arr(ap(good1(), v("N")), pi_("x", bits(), pi_("y", bits(), arr(gb("x"), arr(gb("y"),
        idt(bool0(), sumbit(v("x"), v("y"), v("N")), sumbit(v("y"), v("x"), v("N")))))))))
}
fn proof_c() -> T {
    let gb = |s_: &'static str| pi_("i", nat(0), ap(goodbool(), ap(v(s_), v("i"))));
    let xy = |m: T| st(v("x"), v("y"), m);
    let yx = |m: T| st(v("y"), v("x"), m);
    let pm = lm("M", nat(1), idt(state(), xy(v("M")), yx(v("M"))));
    let r = yx(v("m"));
    let leaf = cases2(
        ap(v("gx"), fst(r.clone())), ap(v("gy"), fst(r.clone())), ap(v("y"), fst(r.clone())), state(),
        &|a, c| pair_s(ap(succ(0), fst(r.clone())), maj(a, c, snd(r.clone()))),
        &|a, c| pair_s(ap(succ(0), fst(r.clone())), maj(c, a, snd(r.clone()))),
    );
    let stepc = lm("m", nat(1), lm("ih", idt(state(), xy(v("m")), yx(v("m"))),
        rew(state(), xy(v("m")), yx(v("m")), v("ih"),
            lm("t", state(), idt(state(), ap(step(v("x"), v("y")), v("t")), ap(step(v("y"), v("x")), yx(v("m"))))),
            leaf)));
    let pn = ap3(v("g"), pm, rfl(pair_s(zero(0), ff())), stepc);
    let r2 = yx(v("N"));
    let leaf2 = cases2(
        ap(v("gx"), fst(r2.clone())), ap(v("gy"), fst(r2.clone())), ap(v("y"), fst(r2.clone())), bool0(),
        &|a, c| xor(xor(a, c), snd(r2.clone())),
        &|a, c| xor(xor(c, a), snd(r2.clone())),
    );
    let fin = rew(state(), xy(v("N")), r2.clone(), pn,
        lm("t", state(), idt(bool0(), sumfn(v("x"), v("y"), v("t")), sumfn(v("y"), v("x"), r2))), leaf2);
    lm("N", nat(1), lm("g", ap(good1(), v("N")), lm("x", bits(), lm("y", bits(),
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
    for (n, t) in [("bool0", bool0()), ("nat0", nat(0)), ("nat1", nat(1)), ("bits", bits()), ("state", state()),
        ("goodbool", goodbool()), ("good1", good1()), ("step", step(v("x"), v("y")))] {
        let _ = n;
        let _ = t;
    }
    // closed pieces
    for (n, t) in [("bool0", bool0()), ("nat1", nat(1)), ("bits", bits()), ("state", state()), ("good1", good1())] {
        if let Err(m) = kernel::typecheck(&ex(&t)) {
            panic!("{n}: {m}");
        }
    }
}

#[test]
fn b_add_zero_uniform() {
    run("b: add x 0 = x, Pi N. Good1 N -> ...", &stmt_b(false), &proof_b(false)).unwrap();
}

#[test]
fn c_add_comm_uniform() {
    run("c: add x y = add y x, Pi N. Good1 N -> ...", &stmt_c(), &proof_c()).unwrap();
}

#[test]
fn d_negative_controls() {
    // (1) the proof skeleton of (b) against the false law add x y = x (y symbolic)
    assert!(run("d1: add x y = x (b-skeleton)", &stmt_b(true), &proof_b(true)).is_err());
    // (2) a false per-bit leaf: xor(xor(a,false),false) = false
    let a_ty = pi_("a", bool0(), arr(ap(goodbool(), v("a")), idt(bool0(), xor(xor(v("a"), ff()), ff()), ff())));
    let a_pf = lm("a", bool0(), lm("ga", ap(goodbool(), v("a")),
        cases1(v("ga"), &|bb| xor(xor(bb, ff()), ff()), &|_| ff())));
    assert!(run("d2: false leaf", &a_ty, &a_pf).is_err());
    // (3) a false law in the same family: the sum bit equals the CARRY-free xor, i.e. add x y = x xor y.
    //     Stated as sumbit = x xor y, with the c-skeleton's leaf (cannot hold: carries differ).
    let bad = pi_("N", nat(1), arr(ap(good1(), v("N")), pi_("x", bits(), pi_("y", bits(),
        idt(bool0(), sumbit(v("x"), v("y"), v("N")), xor(ap(v("x"), embed(v("N"))), ap(v("y"), embed(v("N")))))))));
    // no proof attempt can pass; use the (c) proof as the (wrong-typed) candidate
    assert!(run("d3: add x y = x xor y vs c-proof", &bad, &proof_c()).is_err());
}

#[test]
fn prefix_corollary() {
    // prefix_equal n f g := Pi N. Good1 N -> LE N n -> Id(f N, g N)  with  LE N n := Pi P:(Nat1->Sort1). P N -> (Pi m. P m -> P (succ m)) -> P n
    let le = |a: T, c: T| pi_("P", arr(nat(1), s(1)), arr(ap(v("P"), a),
        arr(pi_("m", nat(1), arr(ap(v("P"), v("m")), ap(v("P"), ap(succ(1), v("m"))))), ap(v("P"), c))));
    let xzero = |n: T| idt(bool0(), sumbit(v("x"), zs(), n.clone()), ap(v("x"), embed(n)));
    let stmt = pi_("n", nat(1), arr(ap(good1(), v("n")), pi_("x", bits(),
        arr(pi_("i", nat(0), ap(goodbool(), ap(v("x"), v("i")))),
            pi_("N", nat(1), arr(ap(good1(), v("N")), arr(le(v("N"), v("n")), xzero(v("N")))))))));
    // proof: ignore n, g, LE; use the pointwise theorem
    let pf = lm("n", nat(1), lm("gn", ap(good1(), v("n")), lm("x", bits(),
        lm("gx", pi_("i", nat(0), ap(goodbool(), ap(v("x"), v("i")))),
            lm("N", nat(1), lm("g", ap(good1(), v("N")), lm("hle", le(v("N"), v("n")),
                ap3(proof_b(false), v("N"), v("g"), v("x")).clone()
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
    let num1 = |k: u32| {
        let mut e = zero(1);
        for _ in 0..k {
            e = ap(succ(1), e);
        }
        e
    };
    let ones = lm("i", nat(0), tt());
    // all-ones + all-ones: bit0 = 0, then carry 1 forever (bits 0,1,1,1)
    let want = [ff(), tt(), tt(), tt()];
    for (k, w) in want.iter().enumerate() {
        let lhs = ex(&sumbit(ones.clone(), ones.clone(), num1(k as u32)));
        assert!(kernel::def_eq(&lhs, &ex(w)), "bit {k} of ones+ones");
    }
    // all-ones + zero = all ones; zero + zero = zero
    assert!(kernel::def_eq(&ex(&sumbit(ones.clone(), zs(), num1(5))), &ex(&tt())));
    assert!(kernel::def_eq(&ex(&sumbit(zs(), zs(), num1(5))), &ex(&ff())));
    // (b) with the right-hand side replaced by `false` must fail with the real proof
    let bad = pi_("N", nat(1), arr(ap(good1(), v("N")), pi_("x", bits(),
        arr(pi_("i", nat(0), ap(goodbool(), ap(v("x"), v("i")))),
            idt(bool0(), sumbit(v("x"), zs(), v("N")), ff())))));
    assert!(run("d4: add x 0 = false", &bad, &proof_b(false)).is_err());
    // (c) false variant: add x y = add y y
    let bad2 = pi_("N", nat(1), arr(ap(good1(), v("N")), pi_("x", bits(), pi_("y", bits(),
        arr(pi_("i", nat(0), ap(goodbool(), ap(v("x"), v("i")))), arr(pi_("i", nat(0), ap(goodbool(), ap(v("y"), v("i")))),
            idt(bool0(), sumbit(v("x"), v("y"), v("N")), sumbit(v("y"), v("y"), v("N")))))))));
    assert!(run("d5: add x y = add y y vs c-proof", &bad2, &proof_c()).is_err());
}
