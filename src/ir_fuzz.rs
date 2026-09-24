//! Differential tests for the lowering templates (step 3 of the JIT IR
//! spec). An IR module is run two ways:
//! 1. through `lower_wat::lower` and wasmtime;
//! 2. through `decompile` and `eval::apply_term`.
//!
//! The results must agree. An interpreter `DivByZero` must match a Wasm
//! trap. The per-template tests cover each template at edge values. The
//! generator produces random well-typed, non-recursive modules under both
//! dispatch modes.

use std::sync::OnceLock;

use crate::decompile::decompile;
use crate::eval::{apply_term, EvalError};
use crate::ir::{check, Combinator, Dispatch, Func, Module, Node, Read};
use crate::lower_wat::lower;
use crate::term::{PrimOp, TermStore};

const EDGES: [i64; 8] = [i64::MIN, i64::MIN + 1, -7, -1, 0, 1, 7, i64::MAX];

fn engine() -> &'static wasmtime::Engine {
    static ENGINE: OnceLock<wasmtime::Engine> = OnceLock::new();
    ENGINE.get_or_init(wasmtime::Engine::default)
}

/// Runs `m` compiled: `Ok(value)` or `Err(())` for a trap.
fn run_wasm(m: &Module, args: &[i64]) -> Result<i64, ()> {
    let frag = lower(m);
    let bytes = wat::parse_str(&frag.wat).expect("lowered WAT parses");
    let module = wasmtime::Module::new(engine(), &bytes).expect("lowered WAT validates");
    let mut store = wasmtime::Store::new(engine(), ());
    let instance = wasmtime::Instance::new(&mut store, &module, &[]).expect("instantiates");
    let f = instance.get_func(&mut store, "f").expect("exports f");
    let wargs: Vec<wasmtime::Val> = args.iter().map(|&a| wasmtime::Val::I64(a)).collect();
    let mut out = [wasmtime::Val::I64(0)];
    f.call(&mut store, &wargs, &mut out).map_err(|_| ())?;
    match out[0] {
        wasmtime::Val::I64(v) => Ok(v),
        _ => panic!("f returned a non-i64"),
    }
}

/// Runs `m` by meaning: the decompiled term, interpreted.
fn run_reference(m: &Module, args: &[i64]) -> Result<i64, EvalError> {
    let mut s = TermStore::new();
    let h = decompile(m, &mut s).expect("a well-formed module decompiles");
    apply_term(&s, h, args)
}

/// Asserts the two agree on `args`. Only a division by zero may fail, and
/// it must fail on both sides.
fn agree(m: &Module, args: &[i64], what: &str) {
    check(m).unwrap_or_else(|e| panic!("{what}: test module is ill-formed: {e}"));
    let wasm = run_wasm(m, args);
    let reference = run_reference(m, args);
    match (&wasm, &reference) {
        (Ok(a), Ok(b)) if a == b => {}
        (Err(()), Err(EvalError::DivByZero)) => {}
        _ => panic!("{what}: args {args:?}: compiled {wasm:?} vs interpreted {reference:?}"),
    }
}

fn b(n: Node) -> Box<Node> {
    Box::new(n)
}
fn p(li: u32) -> Node {
    Node::Read(Read::Param(li))
}
fn e(k: u32) -> Node {
    Node::Read(Read::Env(k))
}
fn entry(arity: usize, is_rec: bool, body: Node, combinators: Vec<Combinator>, dispatch: Dispatch) -> Module {
    Module { entry: Func { arity, is_rec, env_len: 0, body }, combinators, dispatch }
}
fn lifted(arity: usize, env_len: usize, body: Node) -> Combinator {
    Combinator::Lifted(Func { arity, is_rec: false, env_len, body })
}

#[test]
fn arithmetic_templates_agree_at_edge_values() {
    for op in [PrimOp::Add, PrimOp::Sub, PrimOp::Mul, PrimOp::Div, PrimOp::Mod] {
        let m = entry(2, false, Node::Arith(op, b(p(0)), b(p(1))), vec![], Dispatch::Fast);
        for x in EDGES {
            for y in EDGES {
                agree(&m, &[x, y], &format!("{op:?}"));
            }
        }
    }
}

#[test]
fn comparison_templates_agree_at_edge_values() {
    for cmp in [PrimOp::Lt, PrimOp::Le, PrimOp::Eq] {
        let m = entry(2, false, Node::If { cmp, a: b(p(0)), b: b(p(1)), then: b(Node::Lit(1)), els: b(Node::Lit(0)) }, vec![], Dispatch::Fast);
        for x in EDGES {
            for y in EDGES {
                agree(&m, &[x, y], &format!("{cmp:?}"));
            }
        }
    }
}

#[test]
fn tail_and_non_tail_self_call_templates_agree() {
    // rec f n acc = if n <= 0 then acc else f (n - 1) (acc + n), a loop.
    let tail = entry(
        2,
        true,
        Node::If {
            cmp: PrimOp::Le,
            a: b(p(0)),
            b: b(Node::Lit(0)),
            then: b(p(1)),
            els: b(Node::SelfCall { args: vec![Node::Arith(PrimOp::Sub, b(p(0)), b(Node::Lit(1))), Node::Arith(PrimOp::Add, b(p(1)), b(p(0)))], tail: true }),
        },
        vec![],
        Dispatch::Fast,
    );
    // rec f n = if n <= 0 then 0 else n + f (n - 1), a real call.
    let non_tail = entry(
        1,
        true,
        Node::If {
            cmp: PrimOp::Le,
            a: b(p(0)),
            b: b(Node::Lit(0)),
            then: b(Node::Lit(0)),
            els: b(Node::Arith(PrimOp::Add, b(p(0)), b(Node::SelfCall { args: vec![Node::Arith(PrimOp::Sub, b(p(0)), b(Node::Lit(1)))], tail: false }))),
        },
        vec![],
        Dispatch::Fast,
    );
    for n in [i64::MIN, -1, 0, 1, 2, 10, 100] {
        for acc in EDGES {
            agree(&tail, &[n, acc], "tail self-call");
        }
        agree(&non_tail, &[n], "non-tail self-call");
    }
}

/// `\x. (\y. x - y)` as `$c0`, capturing `x` in slot 0.
fn minus_closure() -> Combinator {
    lifted(1, 1, Node::Arith(PrimOp::Sub, b(e(0)), b(p(0))))
}

#[test]
fn closure_templates_agree_under_both_dispatch_modes() {
    for dispatch in [Dispatch::Fast, Dispatch::Curried] {
        // A known call with an environment.
        let known = entry(1, false, Node::CallKnown { f: 0, env: vec![Read::Param(0)], args: vec![Node::Lit(5)] }, vec![minus_closure()], dispatch);
        // An unknown call on a freshly built closure.
        let unknown = entry(
            1,
            false,
            Node::CallUnknown { callee: b(Node::MakeClosure { f: 0, env: vec![Read::Param(0)] }), args: vec![Node::Lit(3)] },
            vec![minus_closure()],
            dispatch,
        );
        // A partial application: (\a b c. (a + b) * c) with `a` captured,
        // `b` supplied, `c` applied later.
        let pap = entry(
            1,
            false,
            Node::CallUnknown { callee: b(Node::MakePap { wrapper: 1, root_env: vec![Read::Param(0)], args: vec![Node::Lit(2)] }), args: vec![Node::Lit(10)] },
            vec![lifted(2, 1, Node::Arith(PrimOp::Mul, b(Node::Arith(PrimOp::Add, b(e(0)), b(p(0)))), b(p(1)))), Combinator::Pap { root: 0, supplied: 1 }],
            dispatch,
        );
        // Over-application: $c0 returns the closure $c1 over its argument.
        let over = entry(
            1,
            false,
            Node::CallUnknown { callee: b(Node::CallKnown { f: 0, env: vec![], args: vec![p(0)] }), args: vec![Node::Lit(4)] },
            vec![lifted(1, 0, Node::MakeClosure { f: 1, env: vec![Read::Param(0)] }), minus_closure()],
            dispatch,
        );
        // A three-argument closure, which under Curried goes through a
        // three-stage chain.
        let three = entry(
            1,
            false,
            Node::CallUnknown {
                callee: b(Node::MakeClosure { f: 0, env: vec![Read::Param(0)] }),
                args: vec![Node::Lit(1), Node::Lit(20), Node::Lit(300)],
            },
            vec![lifted(3, 1, Node::Arith(PrimOp::Sub, b(Node::Arith(PrimOp::Sub, b(Node::Arith(PrimOp::Sub, b(e(0)), b(p(0)))), b(p(1)))), b(p(2))))],
            dispatch,
        );
        for x in EDGES {
            for (m, what) in [(&known, "known call"), (&unknown, "unknown call"), (&pap, "partial application"), (&over, "over-application"), (&three, "three-stage chain")] {
                agree(m, &[x], &format!("{what} ({dispatch:?})"));
            }
        }
    }
}

// ---- Random well-typed IR ---------------------------------------------

/// SplitMix64, the same generator `tests/compile_fuzz.rs` uses.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
}

/// A value's type. Every closure takes `Int` arguments and returns `Int`,
/// which keeps every generated `CallUnknown` well-typed, so the interpreter
/// never type-errors on a correct module.
#[derive(Clone, Copy, PartialEq)]
enum Ty {
    Int,
    Clo(usize),
}

/// The function being generated: the types of its readable values.
struct Scope {
    reads: Vec<(Read, Ty)>,
}

struct Gen<'r> {
    rng: &'r mut Rng,
    combinators: Vec<Combinator>,
}

impl Gen<'_> {
    fn reads_of(&self, sc: &Scope, ty: Ty) -> Vec<Read> {
        sc.reads.iter().filter(|(_, t)| *t == ty).map(|(r, _)| *r).collect()
    }

    fn int(&mut self, sc: &Scope, depth: u32) -> Node {
        let ints = self.reads_of(sc, Ty::Int);
        let leaf = depth == 0 || self.rng.chance(30);
        if leaf {
            if !ints.is_empty() && self.rng.chance(60) {
                return Node::Read(ints[self.rng.below(ints.len())]);
            }
            return Node::Lit(if self.rng.chance(50) { EDGES[self.rng.below(EDGES.len())] } else { self.rng.below(10) as i64 - 3 });
        }
        match self.rng.below(5) {
            0 => {
                let ops = [PrimOp::Add, PrimOp::Sub, PrimOp::Mul, PrimOp::Div, PrimOp::Mod];
                let op = ops[self.rng.below(ops.len())];
                Node::Arith(op, Box::new(self.int(sc, depth - 1)), Box::new(self.int(sc, depth - 1)))
            }
            1 => {
                let cmps = [PrimOp::Lt, PrimOp::Le, PrimOp::Eq];
                let cmp = cmps[self.rng.below(cmps.len())];
                Node::If {
                    cmp,
                    a: Box::new(self.int(sc, depth - 1)),
                    b: Box::new(self.int(sc, depth - 1)),
                    then: Box::new(self.int(sc, depth - 1)),
                    els: Box::new(self.int(sc, depth - 1)),
                }
            }
            2 => {
                let k = 1 + self.rng.below(3);
                let callee = self.clo(sc, k, depth - 1);
                let args = (0..k).map(|_| self.int(sc, depth - 1)).collect();
                Node::CallUnknown { callee: Box::new(callee), args }
            }
            _ => {
                // A known call to a fresh Int-returning lambda. It may take
                // one closure-typed parameter, which exercises reading a
                // closure out of a local.
                let k = 1 + self.rng.below(3);
                let mut params = vec![Ty::Int; k];
                if self.rng.chance(40) {
                    params[self.rng.below(k)] = Ty::Clo(1 + self.rng.below(2));
                }
                let (f, env) = self.fresh_lambda(sc, &params, depth - 1);
                let args = params
                    .iter()
                    .map(|&t| match t {
                        Ty::Int => self.int(sc, depth - 1),
                        Ty::Clo(j) => self.clo(sc, j, depth - 1),
                    })
                    .collect();
                Node::CallKnown { f, env, args }
            }
        }
    }

    /// A closure value taking `k` Ints.
    fn clo(&mut self, sc: &Scope, k: usize, depth: u32) -> Node {
        let own = self.reads_of(sc, Ty::Clo(k));
        if !own.is_empty() && self.rng.chance(50) {
            return Node::Read(own[self.rng.below(own.len())]);
        }
        match self.rng.below(3) {
            0 => {
                let (f, env) = self.fresh_lambda(sc, &vec![Ty::Int; k], depth);
                Node::MakeClosure { f, env }
            }
            1 => {
                // A partial application: a root of arity k + s with s
                // arguments supplied.
                let s = 1 + self.rng.below(2);
                let (root, root_env) = self.fresh_lambda(sc, &vec![Ty::Int; k + s], depth);
                let wrapper = self.combinators.len();
                self.combinators.push(Combinator::Pap { root, supplied: s });
                let args = (0..s).map(|_| self.int(sc, depth.saturating_sub(1))).collect();
                Node::MakePap { wrapper, root_env, args }
            }
            _ => {
                // Over-application's callee: a known call returning a
                // closure.
                let (f, env) = self.fresh_closure_returning(sc, k, depth);
                Node::CallKnown { f, env, args: vec![self.int(sc, depth.saturating_sub(1))] }
            }
        }
    }

    /// Registers a new lambda with parameter types `params` (local `li` has
    /// type `params[li]`), capturing a random subset of `sc`'s reads. It
    /// returns its index and the environment its building site passes.
    fn fresh_lambda(&mut self, sc: &Scope, params: &[Ty], depth: u32) -> (usize, Vec<Read>) {
        let (idx, env, inner) = self.open(sc, params);
        let body = self.int(&inner, depth);
        self.close(idx, params.len(), env.len(), body);
        (idx, env)
    }

    /// Like `fresh_lambda`, with one Int parameter and a body that
    /// returns a `Clo(k)`.
    fn fresh_closure_returning(&mut self, sc: &Scope, k: usize, depth: u32) -> (usize, Vec<Read>) {
        let (idx, env, inner) = self.open(sc, &[Ty::Int]);
        let body = self.clo(&inner, k, depth.saturating_sub(1));
        self.close(idx, 1, env.len(), body);
        (idx, env)
    }

    fn open(&mut self, sc: &Scope, params: &[Ty]) -> (usize, Vec<Read>, Scope) {
        let idx = self.combinators.len();
        self.combinators.push(Combinator::Lifted(Func { arity: 0, is_rec: false, env_len: 0, body: Node::Lit(0) })); // placeholder, filled by `close`
        let captured: Vec<(Read, Ty)> = sc.reads.iter().copied().filter(|_| self.rng.chance(50)).collect();
        let env: Vec<Read> = captured.iter().map(|(r, _)| *r).collect();
        let mut inner = Scope { reads: Vec::new() };
        for (li, &t) in params.iter().enumerate() {
            inner.reads.push((Read::Param(li as u32), t));
        }
        for (k, &(_, t)) in captured.iter().enumerate() {
            inner.reads.push((Read::Env(k as u32), t));
        }
        (idx, env, inner)
    }

    fn close(&mut self, idx: usize, arity: usize, env_len: usize, body: Node) {
        self.combinators[idx] = Combinator::Lifted(Func { arity, is_rec: false, env_len, body });
    }
}

fn random_module(rng: &mut Rng) -> Module {
    let arity = rng.below(3);
    let dispatch = if rng.chance(50) { Dispatch::Fast } else { Dispatch::Curried };
    let mut g = Gen { rng, combinators: Vec::new() };
    let sc = Scope { reads: (0..arity).map(|li| (Read::Param(li as u32), Ty::Int)).collect() };
    let body = g.int(&sc, 4);
    Module { entry: Func { arity, is_rec: false, env_len: 0, body }, combinators: g.combinators, dispatch }
}

fn fuzz(seeds: u64) {
    let mut rng = Rng(0x7A71C);
    for seed in 0..seeds {
        let m = random_module(&mut rng);
        check(&m).unwrap_or_else(|e| panic!("seed {seed}: the generator produced an ill-formed module: {e}"));
        for _ in 0..3 {
            let args: Vec<i64> = (0..m.entry.arity).map(|_| EDGES[rng.below(EDGES.len())]).collect();
            agree(&m, &args, &format!("random module, seed {seed}"));
        }
    }
}

#[test]
fn random_well_typed_modules_agree() {
    fuzz(150);
}

/// The long run, in release: `cargo test --release --lib ir_fuzz -- --ignored`.
#[test]
#[ignore]
fn random_well_typed_modules_agree_long() {
    fuzz(5000);
}
