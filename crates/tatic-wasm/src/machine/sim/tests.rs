//! The generator on straight-line, `If` and self-call bodies: a mini source language mirrors what `tatic::proof::gate::source_fn`
//! reads from a `Term`, so these tests need no term store.
use super::*;
use crate::machine::statement::{statement, statement_with, Clauses, SEnv, SrcFn, FIXED};

#[derive(Clone, Debug)]
enum Src {
    Param(usize),
    Lit(u128),
    /// A word row on two operands.
    Prim(&'static str, Box<Src>, Box<Src>),
    /// `If(cmp, a, b, then, else)`: the bit row `cmp a b` chooses.
    If(&'static str, Box<Src>, Box<Src>, Box<Src>, Box<Src>),
    /// A call of the function itself on its arguments, evaluated left to right.
    SelfCall(Vec<Src>),
    /// A call of the callee at a module position.
    Callee(usize, Vec<Src>),
    /// A closure call as the lowering emits it: the head's environment half (a guarded `shr_u` site, its word
    /// dropped), the arguments, the head again, then `call_dyn` on the head's index word.
    Apply(Box<Src>, Vec<Src>),
    /// `Apply` with the head evaluated once and its word reused for the index (the walk is lockstep, so it must refuse it
    /// against code that evaluates the head twice).
    ApplyOnce(Box<Src>, Vec<Src>),
    /// `Apply` that dispatches through a static call of the module position instead of `call_dyn`.
    ApplyStatic(usize, Box<Src>, Vec<Src>),
}
use Src::*;

fn pr(o: &'static str, a: Src, b: Src) -> Src {
    Prim(o, Box::new(a), Box::new(b))
}
fn iff(o: &'static str, a: Src, b: Src, t: Src, e: Src) -> Src {
    If(o, Box::new(a), Box::new(b), Box::new(t), Box::new(e))
}

/// The arguments of a self-call evaluated left to right, then `k` on their marks.
fn cps_list(w: &Machine, e: &SEnv, c: &mut Cx, args: &[Src], done: Vec<At>, k: &dyn Fn(&mut Cx, &[At]) -> Expr) -> Expr {
    match args.split_first() {
        None => k(c, &done),
        Some((a, rest)) => cps(w, e, c, a, &|c, x| {
            let mut d = done.clone();
            d.push(c.mark(x));
            cps_list(w, e, c, rest, d, k)
        }),
    }
}

/// A word row's site on the marked operands `x`, `y`: `choose(dom x y, k(op x y), z)`.
fn site(w: &Machine, e: &SEnv, c: &mut Cx, o: &str, x: At, y: At, k: &dyn Fn(&mut Cx, Expr) -> Expr) -> Expr {
    let op = (w.table.row(o).unwrap().meaning)(c, w, 0);
    let kk = k(c, app2(op, c.at(x), c.at(y)));
    let dom = constant_n(w.table.row(o).unwrap().dom.circuit, w.n);
    e.choose(c, app2(dom, c.at(x), c.at(y)), kk, c.at(e.z))
}

/// How a closure call's source side finishes after the head's environment half and the arguments.
#[derive(Clone, Copy)]
enum Dispatch {
    Twice,
    Once,
    Static(usize),
}

/// `Apply`: read in the lowering's order (see `Src::Apply`).
fn apply(w: &Machine, e: &SEnv, c: &mut Cx, head: &Src, args: &[Src], k: &dyn Fn(&mut Cx, Expr) -> Expr, how: Dispatch) -> Expr {
    cps(w, e, c, head, &|c, h| {
        let h = c.mark(h);
        let shift = c.mark(lit(e.n, 32));
        site(w, e, c, "shr_u", h, shift, &|c, _env| {
            cps_list(w, e, c, args, vec![], &|c, xs| {
                let index = |c: &mut Cx, h: At| app((w.table.row("wrap").unwrap().meaning)(c, w, 0), c.at(h));
                match how {
                    Dispatch::Once => {
                        let idx = index(c, h);
                        e.call_dyn(c, idx, xs, k)
                    }
                    Dispatch::Twice => cps(w, e, c, head, &|c, h2| {
                        let h2 = c.mark(h2);
                        let idx = index(c, h2);
                        e.call_dyn(c, idx, xs, k)
                    }),
                    Dispatch::Static(pos) => e.call(c, pos, xs, k),
                }
            })
        })
    })
}

fn cps(w: &Machine, e: &SEnv, c: &mut Cx, s: &Src, k: &dyn Fn(&mut Cx, Expr) -> Expr) -> Expr {
    tatic_kernel::grow(|| match s {
        Param(i) => k(c, c.at(e.params[*i])),
        Lit(v) => k(c, lit(e.n, *v)),
        Prim(o, a, b) => cps(w, e, c, a, &|c, x| {
            let x = c.mark(x);
            cps(w, e, c, b, &|c, y| {
                let y = c.mark(y);
                site(w, e, c, o, x, y, k)
            })
        }),
        Apply(head, args) => apply(w, e, c, head, args, k, Dispatch::Twice),
        ApplyOnce(head, args) => apply(w, e, c, head, args, k, Dispatch::Once),
        ApplyStatic(pos, head, args) => apply(w, e, c, head, args, k, Dispatch::Static(*pos)),
        If(o, a, b, t, f) => cps(w, e, c, a, &|c, x| {
            let x = c.mark(x);
            cps(w, e, c, b, &|c, y| {
                let op = (w.table.row(o).unwrap().meaning)(c, w, 0);
                let cond = app2(op, c.at(x), y);
                let (t2, f2) = (cps(w, e, c, t, k), cps(w, e, c, f, k));
                e.choose(c, cond, t2, f2)
            })
        }),
        SelfCall(args) => cps_list(w, e, c, args, vec![], &|c, xs| e.call(c, e.own, xs, k)),
        Callee(pos, args) => cps_list(w, e, c, args, vec![], &|c, xs| e.call(c, *pos, xs, k)),
    })
}

fn get(i: i64) -> Ins {
    Ins::Row { name: "local.get", operand: i }
}
fn konst(v: i64) -> Ins {
    Ins::Row { name: "const", operand: v }
}
fn row(name: &'static str) -> Ins {
    Ins::Row { name, operand: 0 }
}

/// name, arity, code, source
type Case = (&'static str, usize, Vec<Ins>, Src);

/// `\a b. a - b`
fn minus() -> Case {
    ("a - b", 2, vec![get(0), get(1), row("sub")], pr("sub", Param(0), Param(1)))
}
/// `\a b. a % b`: the one partial row, its site guarded by `y != 0`
fn rem() -> Case {
    ("a % b", 2, vec![get(0), get(1), row("mod")], pr("mod", Param(0), Param(1)))
}
/// `\a b. if a < b then a * 2 else b + 1`
fn branch() -> Case {
    let code = vec![get(0), get(1), row("lt"), Ins::If(vec![get(0), konst(2), row("mul")], vec![get(1), konst(1), row("add")])];
    let src = iff("lt", Param(0), Param(1), pr("mul", Param(0), Lit(2)), pr("add", Param(1), Lit(1)));
    ("branch", 2, code, src)
}

/// Prove and check one case on a `CHECK_STACK` thread: `Err` is the generator's refusal or the kernel's.
fn run(n: usize, (_, arity, code, src): &Case) -> Result<(), String> {
    run_with(n, *arity, code, &|w| {
        let src = src.clone();
        Box::new(move |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(w, e, c, &src, k))
    })
}

/// `run` with the source function built by `mk` from the machine (made on the checking thread), so a test can hand
/// the walk a source `cps` would not build.
fn run_with(n: usize, arity: usize, code: &[Ins], mk: &(dyn for<'m> Fn(&'m Machine<'static>) -> Box<SrcFn<'m>> + Sync)) -> Result<(), String> {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn_scoped(s, || {
                let t = crate::wasm::table();
                let w = Machine { n, fw: 0, table: t };
                let entry = Entry { arity, env: EnvAccess::Params(0), code: code.to_vec() };
                let f = mk(&w);
                let module = [Some(ModEntry { entry: &entry, src: &*f })];
                let stmt = statement(&w, &module, 0);
                let proof = prove(&w, &module, 0)?;
                holds(&proof, &stmt)
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

#[test]
fn prove_accepts_straight_line_and_if() {
    for n in [8, 64] {
        for case in [minus(), rem(), branch()] {
            run(n, &case).unwrap_or_else(|e| panic!("n={n} {}: {e}", case.0));
        }
    }
}

/// `\a b. a % b`'s source with a wrong guard, built as `cps` builds it (`y` marked, `k(op x y)` first): the condition
/// the literal 1 in place of `dom x y`, or (`vacuous`) the else `k(op x y)` in place of `z`.
fn wrong_guard<'m>(w: &'m Machine<'static>, vacuous: bool) -> Box<SrcFn<'m>> {
    Box::new(move |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| {
        let row = w.table.row("mod").unwrap();
        let x = e.params[0];
        let y = c.mark(c.at(e.params[1]));
        let op = (row.meaning)(c, w, 0);
        let kk = k(c, app2(op, c.at(x), c.at(y)));
        let dom = app2(constant_n(row.dom.circuit, w.n), c.at(x), c.at(y));
        if vacuous { e.choose(c, dom, kk, kk) } else { e.choose(c, lit(1, 1), kk, c.at(e.z)) }
    })
}
fn guard_always<'m>(w: &'m Machine<'static>) -> Box<SrcFn<'m>> {
    wrong_guard(w, false)
}
fn guard_vacuous<'m>(w: &'m Machine<'static>) -> Box<SrcFn<'m>> {
    wrong_guard(w, true)
}

/// The machine's guard is the table's; a source whose guard differs (always taken, or with no else of its own) is
/// refused by the walk.
#[test]
fn prove_refuses_a_wrong_guard() {
    let (_, arity, code, _) = rem();
    let cases = [
        ("condition 1", guard_always as for<'a> fn(&'a Machine<'static>) -> Box<SrcFn<'a>>, "body: the branch conditions differ"),
        ("else k(op x y)", guard_vacuous, "body/else: the machine is stuck but the source returns"),
    ];
    for (name, mk, want) in cases {
        let err = run_with(8, arity, &code, &mk).expect_err(name);
        assert_eq!(err.to_string(), want, "{name}");
    }
}

/// `z` pinned: out of `mod`'s domain the source side answers the statement's `z`, not `k(op x y)`. The gate shows the
/// machine equals the source, both reading `z` from one binder, so a wrong else on both sides would pass it.
#[test]
fn out_of_domain_answers_z() {
    std::thread::Builder::new()
        .stack_size(tatic_kernel::CHECK_STACK)
        .spawn(|| {
            let n = 8;
            let w0 = Machine { n, fw: 0, table: crate::wasm::table() };
            let (_, arity, code, src) = rem();
            let entry = Entry { arity, env: EnvAccess::Params(0), code };
            let f = |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w0, e, c, &src, k);
            let module = [Some(ModEntry { entry: &entry, src: &f })];
            let w = widen(&w0, &module);
            // R z a ks
            let tys = vec![
                ty!(|_c, _x| sort(0)),
                ty!(|c, x| c.at(x[0])),
                ty!(|_c, _x| bv_ty(n)),
                ty!(|c, x| arrow(bv_ty(n), c.at(x[0]))),
            ];
            let got = tele(&mut Cx::default(), &tys, &mut vec![], &lam, &mut |c, x| {
                let fuel = c.mark(nat2_lit(2));
                let sc = Ctxt::new(c, w, &module, fuel, x[0], x[1]).real(c, 0).sc;
                app3(c.at(sc), c.at(x[2]), lit(n, 0), c.at(x[3]))
            });
            let want = tele(&mut Cx::default(), &tys, &mut vec![], &lam, &mut |c, x| c.at(x[1]));
            assert!(def_eq(&got, &want), "a % 0 does not answer z");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn prove_refuses_a_swapped_if_and_a_wrong_row() {
    let mut swapped = branch();
    let Ins::If(t, e) = swapped.2.last_mut().unwrap() else { panic!() };
    std::mem::swap(t, e);
    let mut wrong = minus();
    wrong.2[2] = row("add");
    for case in [swapped, wrong] {
        let err = run(8, &case).expect_err(case.0);
        assert!(err.starts_with("body"), "{}: the refusal names the path: {err}", case.0);
    }
}

/// `rec f n acc = if n <= 0 then acc else f (n - 1) (acc + n)`, its code pushing the arguments left to right.
fn sum_loop() -> Case {
    let code = vec![
        get(0), konst(0), row("le"),
        Ins::If(vec![get(1)], vec![get(0), konst(1), row("sub"), get(1), get(0), row("add"), Ins::Call(0)]),
    ];
    let src = iff("le", Param(0), Lit(0), Param(1), SelfCall(vec![pr("sub", Param(0), Lit(1)), pr("add", Param(1), Param(0))]));
    ("sum loop", 2, code, src)
}
/// `rec f n = if n <= 1 then 1 else n * f (n - 1)`: a non-tail self-call.
fn factorial() -> Case {
    let code = vec![
        get(0), konst(1), row("le"),
        Ins::If(vec![konst(1)], vec![get(0), get(0), konst(1), row("sub"), Ins::Call(0), row("mul")]),
    ];
    let src = iff("le", Param(0), Lit(1), Lit(1), pr("mul", Param(0), SelfCall(vec![pr("sub", Param(0), Lit(1))])));
    ("factorial", 1, code, src)
}

#[test]
fn prove_accepts_a_sum_loop_and_factorial() {
    for n in [8, 64] {
        for case in [sum_loop(), factorial()] {
            run(n, &case).unwrap_or_else(|e| panic!("n={n} {}: {e}", case.0));
        }
    }
}

/// The sum loop's two argument computations exchanged: slot 0 then holds `acc + n`, not `n - 1`.
#[test]
fn prove_refuses_a_swapped_call_argument() {
    let mut swapped = sum_loop();
    let Ins::If(_, e) = swapped.2.last_mut().unwrap() else { panic!() };
    let (first, second) = (e[..3].to_vec(), e[3..6].to_vec());
    e.splice(..6, second.into_iter().chain(first));
    let err = run(8, &swapped).expect_err("swapped call arguments");
    assert!(err.starts_with("body") && err.contains("local 0"), "the refusal names the path and the slot: {err}");
}

/// A two-entry module: the callee `\a b. a - b` at position 0 and the entry `\x. (g x 1) * 2` at position 1, whose
/// callee law the entry's proof takes as a hypothesis and the callee's closed proof discharges. `swap` makes the entry's
/// code pass its arguments the other way round.
fn two_entries(n: usize, swap: bool) -> Result<(), String> {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn_scoped(s, || {
                let t = crate::wasm::table();
                let w = Machine { n, fw: 0, table: t };
                let callee = Entry { arity: 2, env: EnvAccess::Params(0), code: vec![get(0), get(1), row("sub")] };
                let args = if swap { vec![konst(1), get(0)] } else { vec![get(0), konst(1)] };
                let main = Entry { arity: 1, env: EnvAccess::Params(0), code: [args, vec![Ins::Call(0), konst(2), row("mul")]].concat() };
                let g_src = pr("sub", Param(0), Param(1));
                let f_src = pr("mul", Callee(0, vec![Param(0), Lit(1)]), Lit(2));
                let gf = |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w, e, c, &g_src, k);
                let ff = |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w, e, c, &f_src, k);
                let module = [Some(ModEntry { entry: &callee, src: &gf }), Some(ModEntry { entry: &main, src: &ff })];
                let stmt = statement(&w, &module, 1);
                let proof = prove(&w, &module, 1)?;
                holds(&proof, &stmt)
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

#[test]
fn prove_takes_a_callee_by_its_closed_proof() {
    for n in [8, 64] {
        two_entries(n, false).unwrap_or_else(|e| panic!("n={n}: {e}"));
    }
    let err = two_entries(8, true).expect_err("the entry passes its arguments the wrong way round");
    assert!(err.starts_with("body") && err.contains("local 0"), "{err}");
}

/// The sum loop's real proof against a statement stated under `cl`: the proof is built under the real clauses, so a
/// weakened statement is a different proposition and the kernel must refuse it (O3).
fn sum_loop_against(cl: &Clauses) -> Result<(), String> {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn_scoped(s, || {
                let t = crate::wasm::table();
                let w = Machine { n: 8, fw: 0, table: t };
                let (_, arity, code, src) = sum_loop();
                let entry = Entry { arity, env: EnvAccess::Params(0), code };
                let f = |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(&w, e, c, &src, k);
                let module = [Some(ModEntry { entry: &entry, src: &f })];
                holds(&prove(&w, &module, 0)?, &statement_with(&w, &module, 0, cl))
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

/// A relation that never reads the machine's continuation: `ks a = ks a`.
fn relate_ignores_k(c: &mut Cx, r: At, _km: At, ks: At, a: At, _mu: At) -> Expr {
    id(c.at(r), app(c.at(ks), c.at(a)), app(c.at(ks), c.at(a)))
}

#[test]
fn the_fixed_clauses_state_what_the_proof_proves() {
    sum_loop_against(&FIXED).expect("the sum loop's proof against the unweakened statement");
}

#[test]
fn a_relation_that_ignores_the_continuation_breaks_the_proof() {
    let cl = Clauses { relate: relate_ignores_k, ..FIXED };
    sum_loop_against(&cl).expect_err("the proof is of the statement with the real relation");
}

#[test]
fn an_unquantified_fuel_breaks_the_proof() {
    let cl = Clauses { quantify_fuel: false, ..FIXED };
    sum_loop_against(&cl).expect_err("the proof is of the statement for every fuel");
}

/// `\a. a` through `extend` then `wrap`, built as `cps` builds a site: `k(wrap(extend a))`, behind a `choose` when `guarded`.
fn unary_source<'m>(w: &'m Machine<'static>, guarded: bool) -> Box<SrcFn<'m>> {
    Box::new(move |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| {
        let un = |c: &mut Cx, name: &str, x: Expr| app((w.table.row(name).unwrap().meaning)(c, w, 0), x);
        let inner = un(c, "extend", c.at(e.params[0]));
        let out = un(c, "wrap", inner);
        let kk = k(c, out);
        if guarded { e.choose(c, lit(1, 1), kk, c.at(e.z)) } else { kk }
    })
}
fn unary_plain<'m>(w: &'m Machine<'static>) -> Box<SrcFn<'m>> {
    unary_source(w, false)
}
fn unary_guarded<'m>(w: &'m Machine<'static>) -> Box<SrcFn<'m>> {
    unary_source(w, true)
}

/// A unary row's site is unguarded: `[get 0, extend, wrap]` is proved against a source answering `k(wrap(extend x))`,
/// and refused against the same source behind a `choose` (the machine returns where the source branches).
#[test]
fn a_unary_site_adds_no_branch() {
    let code = [get(0), row("extend"), row("wrap")];
    for n in [8, 64] {
        run_with(n, 1, &code, &unary_plain).unwrap_or_else(|e| panic!("n={n}: {e}"));
    }
    let err = run_with(8, 1, &code, &unary_guarded).expect_err("a guard the machine does not have");
    assert_eq!(err, "body: the machine returns but the source branches");
}

/// One record of a module under test and the mirror source it must simulate; the position is the index.
type Rec = (Entry, Src);

/// `f` over the module `recs`, on a `CHECK_STACK` thread, each record's source function built by `cps`.
fn on_module<T: Send>(n: usize, recs: &[Rec], f: impl FnOnce(&Machine<'static>, &[Option<ModEntry>]) -> T + Send) -> T {
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(tatic_kernel::CHECK_STACK)
            .spawn_scoped(s, || {
                let w = Machine { n, fw: 0, table: crate::wasm::table() };
                let fs: Vec<Box<SrcFn>> = recs
                    .iter()
                    .map(|(_, src)| {
                        let (src, w) = (src.clone(), &w);
                        Box::new(move |c: &mut Cx, e: &SEnv, k: &dyn Fn(&mut Cx, Expr) -> Expr| cps(w, e, c, &src, k)) as Box<SrcFn>
                    })
                    .collect();
                let module: Vec<Option<ModEntry>> = recs.iter().zip(&fs).map(|((e, _), f)| Some(ModEntry { entry: e, src: &**f })).collect();
                f(&w, &module)
            })
            .unwrap()
            .join()
            .unwrap()
    })
}

fn rec(arity: usize, env: EnvAccess, code: Vec<Ins>, src: Src) -> Rec {
    (Entry { arity, env, code }, src)
}

/// `\f. f 5 .. 5` (`args` fives) as the lowering emits it: the head's environment half (`shr_u 32`), the arguments, the
/// head again as an index (`wrap`), then the dispatch.
fn apply_code(args: usize) -> Vec<Ins> {
    [vec![get(0), konst(32), row("shr_u")], vec![konst(5); args], vec![get(0), row("wrap"), Ins::CallIndirect(args)]].concat()
}
fn apply_fives(args: usize) -> Src {
    Apply(Box::new(Param(0)), vec![Lit(5); args])
}

/// The base module of the dynamic-call tests: `\x. x + 1` reached through an environment pointer (position 0), a
/// direct-only `\a b c. a` (1), and the entry `\f. f 5` (2).
fn dyn_records() -> Vec<Rec> {
    vec![
        rec(1, EnvAccess::Pointer, vec![get(0), konst(1), row("add")], pr("add", Param(0), Lit(1))),
        rec(3, EnvAccess::Params(0), vec![get(0)], Param(0)),
        rec(1, EnvAccess::Params(0), apply_code(1), apply_fives(1)),
    ]
}

/// Whether the entry `k`'s real machine side `hc` and source side `sc`, at fuel 3 and the head word `head`, both answer `z`.
fn answers_z(recs: &[Rec], k: usize, head: u128) -> (bool, bool) {
    let n = 64;
    on_module(n, recs, |w0, module| {
        let w = widen(w0, module);
        let tys = || -> Vec<Ty> {
            vec![
                ty!(|_c, _x| sort(0)),
                ty!(|c, x| c.at(x[0])),
                ty!(|c, x| w.mem(c, x[0])),
                ty!(|c, x| {
                    let mem = w.mem(c, x[0]);
                    arrow(bv_ty(n), arrow(mem, c.at(x[0])))
                }),
                ty!(|c, x| arrow(bv_ty(n), c.at(x[0]))),
            ]
        };
        let want = tele(&mut Cx::default(), &tys(), &mut vec![], &lam, &mut |c, x| c.at(x[1]));
        let side = |machine: bool| {
            let got = tele(&mut Cx::default(), &tys(), &mut vec![], &lam, &mut |c, x| {
                let fuel = c.mark(nat2_lit(3));
                let re = Ctxt::new(c, w, module, fuel, x[0], x[1]).real(c, k);
                if machine {
                    app3(c.at(re.hc), w.frame(&[lit(n, head)]), c.at(x[2]), c.at(x[3]))
                } else {
                    app2(c.at(re.sc), lit(n, head), c.at(x[4]))
                }
            });
            def_eq(&got, &want)
        };
        (side(true), side(false))
    })
}

#[test]
fn prove_takes_a_dynamic_call() {
    let recs = dyn_records();
    on_module(64, &recs, |w, module| {
        let stmt = statement(w, module, 2);
        let proof = prove(w, module, 2)?;
        holds(&proof, &stmt)
    })
    .unwrap_or_else(|e| panic!("{e}"));
}

/// A head outside the arity's set answers `z` on both sides, as wasm traps on it: position 1 is not reached through a
/// pointer, 2 is the entry itself, 9 is past the table.
#[test]
fn a_dynamic_call_outside_the_set_answers_z() {
    for head in [1, 2, 9] {
        assert_eq!(answers_z(&dyn_records(), 2, head), (true, true), "head {head}");
    }
}

#[test]
fn a_dynamic_call_of_another_arity_answers_z() {
    let mut recs = dyn_records();
    recs[0].0.arity = 2;
    assert_eq!(answers_z(&recs, 2, 0), (true, true), "the set for arity 1 is empty");
}

/// A closure call wider than every record: the frame is widened to it, so building the callee's frame does not trip
/// `frame`'s assert, and the arity past the table's answers `z`.
#[test]
fn a_closure_call_wider_than_every_record_answers_z() {
    let mut recs = dyn_records();
    recs[2] = rec(1, EnvAccess::Params(0), apply_code(4), apply_fives(4));
    assert_eq!(answers_z(&recs, 2, 0), (true, true));
}

#[test]
fn prove_refuses_a_dynamic_call_against_a_static_one() {
    let mut recs = dyn_records();
    recs[2].1 = ApplyStatic(0, Box::new(Param(0)), vec![Lit(5)]);
    let err = on_module(64, &recs, |w, module| prove(w, module, 2).map(|_| ())).expect_err("the code dispatches, the source calls");
    assert!(err.contains("branches") && err.contains("calls"), "{err}");
}

/// Review Focus 5: the code evaluates the head through `call $c1` twice; a source that calls it once and reuses the
/// word is refused (each machine call needs a source call).
#[test]
fn a_closure_call_with_its_head_evaluated_once_is_rejected() {
    let head = || Callee(1, vec![Param(0)]);
    let code = [vec![get(0), Ins::Call(1), konst(32), row("shr_u"), konst(5), get(0), Ins::Call(1), row("wrap"), Ins::CallIndirect(1)]].concat();
    let mut recs = dyn_records();
    recs[1] = rec(1, EnvAccess::Params(0), vec![get(0)], Param(0));
    recs[2] = rec(1, EnvAccess::Params(0), code, Apply(Box::new(head()), vec![Lit(5)]));
    on_module(64, &recs, |w, module| holds(&prove(w, module, 2)?, &statement(w, module, 2)))
        .unwrap_or_else(|e| panic!("the head evaluated twice on both sides: {e}"));
    recs[2].1 = ApplyOnce(Box::new(head()), vec![Lit(5)]);
    let err = on_module(64, &recs, |w, module| prove(w, module, 2).map(|_| ())).expect_err("the head is evaluated once");
    assert!(err.contains("the machine calls a function but the source"), "{err}");
}

#[test]
fn a_dynamic_cycle_is_found() {
    let reach = vec![get(0), konst(32), row("shr_u"), konst(1), get(0), row("wrap"), Ins::CallIndirect(1)];
    let (a, mut b) = (Entry { arity: 1, env: EnvAccess::Pointer, code: reach.clone() }, Entry { arity: 1, env: EnvAccess::Pointer, code: reach });
    assert!(call_cycle(&[Some(&a), Some(&b)]).is_some());
    b.code = vec![get(0)];
    assert_eq!(call_cycle(&[Some(&a), Some(&b)]), None, "a self-edge and an edge to 1 are no cycle");
}

/// `prove` refuses a cyclic module itself, in a release build too, for a caller that skipped the gate's `call_cycle`.
#[test]
fn prove_refuses_a_dynamic_cycle() {
    let reach = vec![get(0), konst(32), row("shr_u"), konst(1), get(0), row("wrap"), Ins::CallIndirect(1)];
    let recs = vec![rec(1, EnvAccess::Pointer, reach.clone(), Param(0)), rec(1, EnvAccess::Pointer, reach, Param(0))];
    let err = on_module(64, &recs, |w, module| prove(w, module, 0).map(|_| ())).expect_err("a cycle is refused");
    assert!(err.contains("cycle"), "{err}");
}
