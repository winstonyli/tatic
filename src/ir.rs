//! The JIT's intermediate representation, between `compile.rs`'s term
//! analysis (`compile::build`) and `lower_wat.rs`'s WAT templates. It is
//! closure-converted but representation-neutral. It records which function,
//! which local, which environment slot and which kind of call. How a
//! closure is packed, where its environment lives and which scratch locals
//! a template uses are left to the lowering. See
//! `docs/superpowers/specs/2026-09-23-jit-ir-design.md` for why this level
//! was chosen, and for what the later decompiler (step 2) will check
//! against it.
//!
//! Every field is either read by both the lowering and the decompiler,
//! read by the decompiler alone and unable to change runtime meaning, or
//! read by the lowering alone as a representation choice that `check`
//! validates. This is the spec's "field parity". It is what keeps the
//! step-2 decompile check from being vacuous.

use hashbrown::HashMap;

use crate::compile::is_comparison;
use crate::term::PrimOp;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Module {
    /// `$f`. It never has an environment.
    pub entry: Func,
    /// Position is table index is the `$c{idx}` name.
    pub combinators: Vec<Combinator>,
    pub dispatch: Dispatch,
}

/// How a `CallUnknown` is lowered. It is one choice for the whole module:
/// with no type system, nothing proves that a closure value never reaches a
/// variable called at another arity. `Curried` is required as soon as any
/// variable anywhere is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Dispatch {
    Fast,
    Curried,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Combinator {
    /// A lambda literal, closure-converted.
    Lifted(Func),
    /// A partial-application wrapper for combinator `root` with `supplied`
    /// of its arguments already given. Its body is a fixed lowering
    /// template (`emit_pap_wrapper`), so the IR holds none.
    Pap { root: usize, supplied: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Func {
    pub arity: usize,
    pub is_rec: bool,
    /// Number of environment slots. Every site that builds this function's
    /// closure supplies exactly this many.
    pub env_len: usize,
    pub body: Node,
}

/// A value read: a Wasm parameter local (`$p{li}`, which is *not* the de
/// Bruijn index -- see `compile::local_index`), or an environment slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Read {
    Param(u32),
    Env(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Node {
    Lit(i64),
    Read(Read),
    Arith(PrimOp, Box<Node>, Box<Node>),
    If { cmp: PrimOp, a: Box<Node>, b: Box<Node>, then: Box<Node>, els: Box<Node> },
    /// `tail` picks a loop-back or an ordinary `call`. Both are correct;
    /// `check` only forbids `tail: true` outside tail position.
    SelfCall { args: Vec<Node>, tail: bool },
    /// A saturated call to a statically known combinator.
    CallKnown { f: usize, env: Vec<Read>, args: Vec<Node> },
    /// A call through a closure value of unknown arity. Over-application is
    /// `CallUnknown { callee: CallKnown{..}, .. }`, not a node of its own.
    CallUnknown { callee: Box<Node>, args: Vec<Node> },
    MakeClosure { f: usize, env: Vec<Read> },
    /// A partial application: the wrapper's closure over `root`'s
    /// environment plus the supplied arguments.
    MakePap { wrapper: usize, root_env: Vec<Read>, args: Vec<Node> },
}

impl Node {
    /// Every direct child node, in evaluation order. Environments hold
    /// `Read`s, not nodes, so they are not included.
    pub(crate) fn children(&self) -> Vec<&Node> {
        match self {
            Node::Lit(_) | Node::Read(_) | Node::MakeClosure { .. } => vec![],
            Node::Arith(_, a, b) => vec![&**a, &**b],
            Node::If { a, b, then, els, .. } => vec![&**a, &**b, &**then, &**els],
            Node::SelfCall { args, .. } | Node::CallKnown { args, .. } | Node::MakePap { args, .. } => args.iter().collect(),
            Node::CallUnknown { callee, args } => std::iter::once(&**callee).chain(args).collect(),
        }
    }
}

impl Module {
    /// `$f`, then every `Lifted` combinator in index order.
    pub(crate) fn funcs(&self) -> impl Iterator<Item = &Func> {
        std::iter::once(&self.entry).chain(self.combinators.iter().filter_map(|c| match c {
            Combinator::Lifted(f) => Some(f),
            Combinator::Pap { .. } => None,
        }))
    }
}

/// Checks the spec's well-formedness rules. The lowering assumes every one
/// of them and does not re-check. A failure means a builder bug; the term
/// is rejected, never miscompiled.
pub(crate) fn check(m: &Module) -> Result<(), String> {
    if m.entry.env_len != 0 {
        return Err("$f has an environment".into());
    }
    check_func(m, &m.entry).map_err(|e| format!("$f: {e}"))?;
    for (idx, c) in m.combinators.iter().enumerate() {
        match c {
            Combinator::Lifted(f) => check_func(m, f).map_err(|e| format!("$c{idx}: {e}"))?,
            Combinator::Pap { root, supplied } => {
                let r = lifted(m, *root)?;
                if *supplied == 0 || *supplied >= r.arity {
                    return Err(format!("$c{idx}: a partial application supplying {supplied} of {} arguments", r.arity));
                }
            }
        }
    }
    Ok(())
}

fn lifted(m: &Module, idx: usize) -> Result<&Func, String> {
    match m.combinators.get(idx) {
        Some(Combinator::Lifted(f)) => Ok(f),
        Some(Combinator::Pap { .. }) => Err(format!("$c{idx} is a partial-application wrapper, not a lambda")),
        None => Err(format!("there is no $c{idx}")),
    }
}

fn check_func(m: &Module, f: &Func) -> Result<(), String> {
    check_node(m, f, &f.body, true, &mut HashMap::new())
}

fn check_read(f: &Func, r: Read) -> Result<(), String> {
    match r {
        Read::Param(li) if (li as usize) < f.arity => Ok(()),
        Read::Env(k) if (k as usize) < f.env_len => Ok(()),
        _ => Err(format!("{r:?} is out of range (arity {}, env_len {})", f.arity, f.env_len)),
    }
}

fn check_env(f: &Func, expected_len: usize, env: &[Read]) -> Result<(), String> {
    if env.len() != expected_len {
        return Err(format!("an environment of {} slots for a function expecting {expected_len}", env.len()));
    }
    env.iter().try_for_each(|r| check_read(f, *r))
}

/// `callee_arities` records, for this function, how many arguments each
/// `Read` callee has been applied to so far. Under `Dispatch::Fast` they
/// must all agree.
fn check_node(m: &Module, f: &Func, n: &Node, tail: bool, callee_arities: &mut HashMap<Read, usize>) -> Result<(), String> {
    match n {
        Node::Lit(_) => {}
        Node::Read(r) => check_read(f, *r)?,
        Node::Arith(op, ..) => {
            if is_comparison(*op) {
                return Err(format!("{op:?} used as arithmetic"));
            }
        }
        Node::If { cmp, .. } => {
            if !is_comparison(*cmp) {
                return Err(format!("{cmp:?} used as a condition"));
            }
        }
        Node::SelfCall { args, tail: t } => {
            if !f.is_rec {
                return Err("a self-call in a non-recursive function".into());
            }
            if args.len() != f.arity {
                return Err(format!("a self-call with {} of {} arguments", args.len(), f.arity));
            }
            if *t && !tail {
                return Err("a tail self-call outside tail position".into());
            }
        }
        Node::CallKnown { f: g, env, args } => {
            let gf = lifted(m, *g)?;
            if args.len() != gf.arity {
                return Err(format!("a known call to $c{g} with {} of {} arguments", args.len(), gf.arity));
            }
            check_env(f, gf.env_len, env)?;
        }
        Node::CallUnknown { callee, args } => {
            if m.dispatch == Dispatch::Fast
                && let Node::Read(r) = **callee
            {
                let k = *callee_arities.entry(r).or_insert(args.len());
                if k != args.len() {
                    return Err(format!("{r:?} called with both {k} and {} arguments under Fast dispatch", args.len()));
                }
            }
        }
        Node::MakeClosure { f: g, env } => check_env(f, lifted(m, *g)?.env_len, env)?,
        Node::MakePap { wrapper, root_env, args } => {
            let Some(Combinator::Pap { root, supplied }) = m.combinators.get(*wrapper) else {
                return Err(format!("$c{wrapper} is not a partial-application wrapper"));
            };
            if *supplied != args.len() {
                return Err(format!("a partial application of $c{wrapper} with {} arguments, but it supplies {supplied}", args.len()));
            }
            check_env(f, lifted(m, *root)?.env_len, root_env)?;
        }
    }
    if let Node::If { a, b, then, els, .. } = n {
        check_node(m, f, a, false, callee_arities)?;
        check_node(m, f, b, false, callee_arities)?;
        check_node(m, f, then, tail, callee_arities)?;
        return check_node(m, f, els, tail, callee_arities);
    }
    n.children().into_iter().try_for_each(|c| check_node(m, f, c, false, callee_arities))
}

/// Hand-built terms together with the IR `compile::build` must produce for
/// them. `lower_wat`'s tests use them to pin the lowering to the legacy
/// WAT; `compile`'s tests use them to pin the builder.
#[cfg(test)]
pub(crate) mod fixtures {
    use super::*;
    use crate::term::{Hash, TermStore};

    fn b(n: Node) -> Box<Node> {
        Box::new(n)
    }

    /// `rec f n = if n <= 1 then 1 else n * f(n - 1)`
    pub(crate) fn factorial() -> (TermStore, Hash, Module) {
        let mut s = TermStore::new();
        let n = s.var(0);
        let f = s.var(1);
        let one = s.lit(1);
        let cond = s.prim(PrimOp::Le, n, one);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(f, n_minus_1);
        let else_branch = s.prim(PrimOp::Mul, n, rec_call);
        let body = s.if_(cond, one, else_branch);
        let abs = s.abs(body);
        let h = s.rec(abs);
        let p0 = || Node::Read(Read::Param(0));
        let m = Module {
            entry: Func {
                arity: 1,
                is_rec: true,
                env_len: 0,
                body: Node::If {
                    cmp: PrimOp::Le,
                    a: b(p0()),
                    b: b(Node::Lit(1)),
                    then: b(Node::Lit(1)),
                    els: b(Node::Arith(
                        PrimOp::Mul,
                        b(p0()),
                        b(Node::SelfCall { args: vec![Node::Arith(PrimOp::Sub, b(p0()), b(Node::Lit(1)))], tail: false }),
                    )),
                },
            },
            combinators: vec![],
            dispatch: Dispatch::Fast,
        };
        (s, h, m)
    }

    /// `\f x. f (f x)`: `f` is `Var(1)` (local `$p0`), `x` is `Var(0)` (`$p1`).
    pub(crate) fn twice() -> (TermStore, Hash, Module) {
        let mut s = TermStore::new();
        let h = twice_term(&mut s);
        let f = || b(Node::Read(Read::Param(0)));
        let m = Module {
            entry: Func {
                arity: 2,
                is_rec: false,
                env_len: 0,
                body: Node::CallUnknown { callee: f(), args: vec![Node::CallUnknown { callee: f(), args: vec![Node::Read(Read::Param(1))] }] },
            },
            combinators: vec![],
            dispatch: Dispatch::Fast,
        };
        (s, h, m)
    }

    /// `(\f x. f (f x)) (\y. y + 1) 5`: `twice` becomes `$c0`, called
    /// directly; `inc` becomes `$c1`, passed as a closure value.
    pub(crate) fn twice_inc() -> (TermStore, Hash, Module) {
        let mut s = TermStore::new();
        let t = twice_term(&mut s);
        let y = s.var(0);
        let one = s.lit(1);
        let y1 = s.prim(PrimOp::Add, y, one);
        let inc = s.abs(y1);
        let five = s.lit(5);
        let h = s.app2(t, inc, five);
        let (_, _, twice_ir) = twice();
        let m = Module {
            entry: Func {
                arity: 0,
                is_rec: false,
                env_len: 0,
                body: Node::CallKnown { f: 0, env: vec![], args: vec![Node::MakeClosure { f: 1, env: vec![] }, Node::Lit(5)] },
            },
            combinators: vec![
                Combinator::Lifted(twice_ir.entry),
                Combinator::Lifted(Func {
                    arity: 1,
                    is_rec: false,
                    env_len: 0,
                    body: Node::Arith(PrimOp::Add, b(Node::Read(Read::Param(0))), b(Node::Lit(1))),
                }),
            ],
            dispatch: Dispatch::Fast,
        };
        (s, h, m)
    }

    fn twice_term(s: &mut TermStore) -> Hash {
        let f = s.var(1);
        let x = s.var(0);
        let fx = s.app(f, x);
        let ffx = s.app(f, fx);
        let inner = s.abs(ffx);
        s.abs(inner)
    }
}

#[cfg(test)]
mod tests {
    use super::fixtures::*;
    use super::*;

    fn lit(n: i64) -> Box<Node> {
        Box::new(Node::Lit(n))
    }

    fn with_entry(body: Node, arity: usize, is_rec: bool) -> Module {
        Module { entry: Func { arity, is_rec, env_len: 0, body }, combinators: vec![], dispatch: Dispatch::Fast }
    }

    fn rejects(m: &Module, needle: &str) {
        let err = check(m).expect_err("should be ill-formed");
        assert!(err.contains(needle), "expected an error mentioning {needle:?}, got {err:?}");
    }

    #[test]
    fn funcs_enumerates_the_entry_then_every_lifted_combinator_in_order() {
        let (_, _, m) = twice_inc();
        let funcs: Vec<&Func> = m.funcs().collect();
        assert_eq!(funcs.len(), 3);
        assert!(std::ptr::eq(funcs[0], &m.entry));
        let Combinator::Lifted(c0) = &m.combinators[0] else { panic!("expected $c0 to be lifted") };
        let Combinator::Lifted(c1) = &m.combinators[1] else { panic!("expected $c1 to be lifted") };
        assert!(std::ptr::eq(funcs[1], c0));
        assert!(std::ptr::eq(funcs[2], c1));
    }

    #[test]
    fn every_fixture_is_well_formed() {
        for (_, _, m) in [factorial(), twice(), twice_inc()] {
            check(&m).unwrap();
        }
    }

    #[test]
    fn the_entry_function_cannot_have_an_environment() {
        let (_, _, mut m) = factorial();
        m.entry.env_len = 1;
        rejects(&m, "has an environment");
    }

    #[test]
    fn a_read_must_be_in_range() {
        rejects(&with_entry(Node::Read(Read::Param(1)), 1, false), "out of range");
        rejects(&with_entry(Node::Read(Read::Env(0)), 1, false), "out of range");
    }

    #[test]
    fn a_comparison_is_not_arithmetic_and_arithmetic_is_not_a_condition() {
        rejects(&with_entry(Node::Arith(PrimOp::Lt, lit(1), lit(2)), 0, false), "used as arithmetic");
        let bad_if = Node::If { cmp: PrimOp::Add, a: lit(1), b: lit(2), then: lit(3), els: lit(4) };
        rejects(&with_entry(bad_if, 0, false), "used as a condition");
    }

    #[test]
    fn a_self_call_needs_a_recursive_function_saturation_and_tail_position_for_tail() {
        let call = |tail| Node::SelfCall { args: vec![Node::Lit(0)], tail };
        rejects(&with_entry(call(false), 1, false), "non-recursive");
        rejects(&with_entry(Node::SelfCall { args: vec![], tail: false }, 1, true), "0 of 1");
        rejects(&with_entry(Node::Arith(PrimOp::Add, Box::new(call(true)), lit(1)), 1, true), "outside tail position");
        check(&with_entry(call(true), 1, true)).unwrap();
        let in_branch = Node::If { cmp: PrimOp::Lt, a: lit(0), b: lit(1), then: Box::new(call(true)), els: lit(2) };
        check(&with_entry(in_branch, 1, true)).unwrap();
    }

    #[test]
    fn a_known_call_must_saturate_a_lambda_with_a_matching_environment() {
        let (_, _, mut m) = twice_inc();
        m.entry.body = Node::CallKnown { f: 0, env: vec![], args: vec![Node::Lit(5)] };
        rejects(&m, "1 of 2");
        m.entry.body = Node::MakeClosure { f: 1, env: vec![Read::Param(0)] };
        m.entry.arity = 1;
        rejects(&m, "environment of 1 slots");
        m.combinators.push(Combinator::Pap { root: 0, supplied: 1 });
        m.entry.body = Node::CallKnown { f: 2, env: vec![], args: vec![Node::Lit(1)] };
        rejects(&m, "not a lambda");
    }

    #[test]
    fn a_partial_application_must_match_its_wrapper() {
        let (_, _, mut m) = twice_inc();
        m.combinators.push(Combinator::Pap { root: 0, supplied: 1 });
        m.entry.body = Node::MakePap { wrapper: 2, root_env: vec![], args: vec![Node::Lit(1), Node::Lit(2)] };
        rejects(&m, "it supplies 1");
        m.entry.body = Node::MakePap { wrapper: 1, root_env: vec![], args: vec![Node::Lit(1)] };
        rejects(&m, "not a partial-application wrapper");
        m.entry.body = Node::Lit(0);
        m.combinators[2] = Combinator::Pap { root: 0, supplied: 2 };
        rejects(&m, "supplying 2 of 2");
    }

    #[test]
    fn fast_dispatch_needs_one_arity_per_callee() {
        let p0 = || Box::new(Node::Read(Read::Param(0)));
        let one = Node::CallUnknown { callee: p0(), args: vec![Node::Lit(1)] };
        let two = Node::CallUnknown { callee: p0(), args: vec![Node::Lit(1), Node::Lit(2)] };
        let mut m = with_entry(Node::Arith(PrimOp::Add, Box::new(one), Box::new(two)), 1, false);
        rejects(&m, "under Fast dispatch");
        m.dispatch = Dispatch::Curried;
        check(&m).unwrap();
    }
}
