//! Translation validation for the JIT: step 2 of
//! `docs/superpowers/specs/2026-09-23-jit-ir-design.md`. It rebuilds, from
//! an `ir::Module` alone, the term that module claims to implement.
//! `compile::try_compile` accepts a module only if the rebuilt term has the
//! source's content hash. A content hash depends only on the term's
//! structure, not on which store interned it (`term::Term::content_hash`),
//! so the rebuild goes into a scratch `TermStore` and never reads the source.
//!
//! The rules invert the *meaning* of each lowering template. Each reads
//! exactly the fields the spec's field-parity classes 1 and 2 name, and
//! nothing the builder alone knows. This file shares nothing with the
//! compiler but the IR and term types: no `classify`, `peel`,
//! `local_index` or `free_vars`. A bug in one of those therefore cannot be
//! mirrored here and cancel itself out. A test enforces the separation.

use hashbrown::HashMap;

use crate::ir::{Combinator, Func, Module, Node, Read};
use crate::term::{Hash, TermStore};

/// The term `m` implements, built into `s`. `None` if `m` refers to
/// something that does not exist: a combinator index out of range, a read
/// out of range, a self-call in a non-recursive function, or a
/// partial-application wrapper that isn't one.
///
/// `ir::check(m).is_ok()` is a precondition, not something this function
/// re-derives: `compile::try_compile` only ever calls it on a checked
/// module, and termination relies on the acyclicity `check_acyclic`
/// establishes (an unchecked cyclic module can recurse forever instead of
/// returning `None`). Fields `check` also verifies -- `saturation`,
/// `env_len`, a `Read`'s `supplied` -- are taken as given here too. The
/// `None` returns above exist only as defense in depth, in case this is
/// ever called on an unchecked module; they are not a substitute for
/// `check` and do not make this function independent of it.
pub(crate) fn decompile(m: &Module, s: &mut TermStore) -> Option<Hash> {
    let mut d = Decompiler { m, s, memo: HashMap::new() };
    d.func(&m.entry, &[])
}

struct Decompiler<'m, 's> {
    m: &'m Module,
    s: &'s mut TermStore,
    /// A closure's term depends on its combinator and on which outer
    /// variables its environment holds, so it is memoised on both.
    memo: HashMap<(usize, Vec<u32>), Hash>,
}

impl Decompiler<'_, '_> {
    /// `f` as a term, when its environment slot `k` holds the outer
    /// variable `env[k]`, a de Bruijn index in the scope that built the
    /// closure. `Rec` is outermost, as `compile::peel` expects.
    fn func(&mut self, f: &Func, env: &[u32]) -> Option<Hash> {
        let mut t = self.node(f, env, &f.body)?;
        for _ in 0..f.arity {
            t = self.s.abs(t);
        }
        if f.is_rec {
            t = self.s.rec(t);
        }
        Some(t)
    }

    /// The de Bruijn index `r` denotes inside `f`'s body.
    ///
    /// Parameters are numbered innermost-first, while Wasm locals are
    /// numbered left to right, so local `$p{li}` is `Var(arity - 1 - li)`.
    ///
    /// A body has no binders of its own, because every nested lambda is its
    /// own combinator. An environment slot's outer variable therefore sits
    /// past `f`'s parameters and, for a recursive `f`, past `Rec`'s self
    /// binder.
    fn var(f: &Func, env: &[u32], r: Read) -> Option<u32> {
        let arity = u32::try_from(f.arity).ok()?;
        match r {
            Read::Param(li) => (li < arity).then(|| arity - 1 - li),
            Read::Env(k) => Some(env.get(k as usize)? + arity + u32::from(f.is_rec)),
        }
    }

    fn node(&mut self, f: &Func, env: &[u32], n: &Node) -> Option<Hash> {
        Some(match n {
            Node::Lit(v) => self.s.lit(*v),
            Node::Read(r) => {
                let v = Self::var(f, env, *r)?;
                self.s.var(v)
            }
            Node::Arith(op, a, b) => {
                let a = self.node(f, env, a)?;
                let b = self.node(f, env, b)?;
                self.s.prim(*op, a, b)
            }
            Node::If { cmp, a, b, then, els } => {
                let a = self.node(f, env, a)?;
                let b = self.node(f, env, b)?;
                let c = self.s.prim(*cmp, a, b);
                let t = self.node(f, env, then)?;
                let e = self.node(f, env, els)?;
                self.s.if_(c, t, e)
            }
            // `tail` is deliberately not read: a loop-back and a `call`
            // mean the same thing (field-parity class 2).
            Node::SelfCall { args, .. } => {
                if !f.is_rec {
                    return None;
                }
                let me = self.s.var(u32::try_from(f.arity).ok()?);
                self.apply(f, env, me, args)?
            }
            Node::CallKnown { f: g, env: reads, args } => {
                let callee = self.closure(f, env, *g, reads)?;
                self.apply(f, env, callee, args)?
            }
            Node::CallUnknown { callee, args } => {
                let callee = self.node(f, env, callee)?;
                self.apply(f, env, callee, args)?
            }
            Node::MakeClosure { f: g, env: reads } => self.closure(f, env, *g, reads)?,
            // A partial application is the root lambda applied to the
            // supplied arguments. `supplied` is class 3 and not read.
            Node::MakePap { wrapper, root_env, args } => {
                let Some(Combinator::Pap { root, .. }) = self.m.combinators.get(*wrapper) else {
                    return None;
                };
                let root = *root;
                let callee = self.closure(f, env, root, root_env)?;
                self.apply(f, env, callee, args)?
            }
        })
    }

    /// `callee` applied to `args` left to right: `App(App(callee, a0), a1)`.
    fn apply(&mut self, f: &Func, env: &[u32], callee: Hash, args: &[Node]) -> Option<Hash> {
        let mut t = callee;
        for a in args {
            let a = self.node(f, env, a)?;
            t = self.s.app(t, a);
        }
        Some(t)
    }

    /// The lambda literal that combinator `g` stands for, when a site in
    /// `f` builds it with environment reads `reads`.
    fn closure(&mut self, f: &Func, env: &[u32], g: usize, reads: &[Read]) -> Option<Hash> {
        let outer: Vec<u32> = reads.iter().map(|&r| Self::var(f, env, r)).collect::<Option<_>>()?;
        if let Some(&h) = self.memo.get(&(g, outer.clone())) {
            return Some(h);
        }
        // Copied out from `&mut self` so the borrow below doesn't have to
        // live across the `&mut self.s` borrows inside `self.func`.
        let m = self.m;
        let Some(Combinator::Lifted(gf)) = m.combinators.get(g) else {
            return None;
        };
        let h = self.func(gf, &outer)?;
        self.memo.insert((g, outer), h);
        Some(h)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::fixtures::{factorial, twice, twice_inc};
    use crate::term::PrimOp;

    fn roundtrips(m: &Module, h: Hash) -> bool {
        decompile(m, &mut TermStore::new()) == Some(h)
    }

    #[test]
    fn each_fixture_decompiles_to_its_source_term() {
        for (_, h, m) in [factorial(), twice(), twice_inc()] {
            assert!(roundtrips(&m, h));
        }
    }

    #[test]
    fn every_built_corpus_module_decompiles_to_its_source_hash() {
        // No false alarms on the real corpus: a correct compilation must
        // always pass the gate.
        for (name, s, h) in crate::test_corpus::terms() {
            let m = crate::compile::build(&s, h).unwrap_or_else(|| panic!("{name} builds"));
            assert!(roundtrips(&m, h), "{name} does not decompile to its source hash");
        }
    }

    #[test]
    fn a_dangling_reference_decompiles_to_nothing() {
        let (_, _, mut m) = twice_inc();
        m.entry.body = Node::MakeClosure { f: 9, env: vec![] };
        assert_eq!(decompile(&m, &mut TermStore::new()), None);
        m.entry.body = Node::Read(Read::Param(0)); // entry arity is 0
        assert_eq!(decompile(&m, &mut TermStore::new()), None);
        m.entry.body = Node::SelfCall { args: vec![], tail: false }; // entry is not recursive
        assert_eq!(decompile(&m, &mut TermStore::new()), None);
        m.entry.body = Node::MakePap { wrapper: 0, root_env: vec![], args: vec![Node::Lit(1)] }; // $c0 is Lifted, not Pap
        assert_eq!(decompile(&m, &mut TermStore::new()), None);
    }

    #[test]
    fn an_environment_slot_resolves_through_the_building_sites_environment() {
        // \x. (\y. x - y) 5, with x captured in slot 0 of $c0.
        let mut s = TermStore::new();
        let x_inner = s.var(1);
        let y = s.var(0);
        let body = s.prim(PrimOp::Sub, x_inner, y);
        let lam = s.abs(body);
        let five = s.lit(5);
        let call = s.app(lam, five);
        let h = s.abs(call);
        let m = Module {
            entry: Func { arity: 1, is_rec: false, env_len: 0, body: Node::CallKnown { f: 0, env: vec![Read::Param(0)], args: vec![Node::Lit(5)] } },
            combinators: vec![Combinator::Lifted(Func {
                arity: 1,
                is_rec: false,
                env_len: 1,
                body: Node::Arith(PrimOp::Sub, Box::new(Node::Read(Read::Env(0))), Box::new(Node::Read(Read::Param(0)))),
            })],
            dispatch: crate::ir::Dispatch::Fast,
        };
        assert!(roundtrips(&m, h));
    }

    #[test]
    fn an_environment_slot_in_a_recursive_combinator_is_offset_past_its_self_binder() {
        // \x. (rec g n. if n <= 0 then x else g (n - 1)) 3, with x captured
        // in slot 0 of a *recursive* $c0. Inside `rec g n`'s own scope:
        // n = Var(0) (nearest), g = Var(1) (Rec's self binder), x = Var(2)
        // (captured from the outer \x). This is the shape
        // `an_environment_slot_resolves_through_the_building_sites_environment`
        // doesn't cover: there, $c0 is not recursive, so the `+
        // u32::from(f.is_rec)` term in `var`'s `Read::Env` arm is always 0.
        let mut s = TermStore::new();
        let n = s.var(0);
        let g = s.var(1);
        let x = s.var(2);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Le, n, zero);
        let one = s.lit(1);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let g_call = s.app(g, n_minus_1);
        let body = s.if_(cond, x, g_call);
        let abs_n = s.abs(body);
        let rec_g = s.rec(abs_n);
        let three = s.lit(3);
        let applied = s.app(rec_g, three);
        let h = s.abs(applied);
        let m = Module {
            entry: Func { arity: 1, is_rec: false, env_len: 0, body: Node::CallKnown { f: 0, env: vec![Read::Param(0)], args: vec![Node::Lit(3)] } },
            combinators: vec![Combinator::Lifted(Func {
                arity: 1,
                is_rec: true,
                env_len: 1,
                body: Node::If {
                    cmp: PrimOp::Le,
                    a: Box::new(Node::Read(Read::Param(0))),
                    b: Box::new(Node::Lit(0)),
                    then: Box::new(Node::Read(Read::Env(0))),
                    els: Box::new(Node::SelfCall {
                        args: vec![Node::Arith(PrimOp::Sub, Box::new(Node::Read(Read::Param(0))), Box::new(Node::Lit(1)))],
                        tail: true,
                    }),
                },
            })],
            dispatch: crate::ir::Dispatch::Fast,
        };
        assert!(roundtrips(&m, h));
        // The fixture is real: it is exactly what `compile::build` produces
        // for this source term, not just a module the decompiler happens to
        // accept.
        assert_eq!(crate::compile::build(&s, h), Some(m));
    }

    #[test]
    fn the_decompiler_imports_nothing_from_the_compiler() {
        // The whole point of the check is that a bug in `compile.rs`'s or
        // `lower_wat.rs`'s helpers cannot be mirrored here. Enforced
        // mechanically: token by token (so `use crate :: compile :: peel;`
        // or `use crate::{compile::peel};` can't slip past a substring
        // match), and only over the code above `mod tests`, so
        // `crate::compile::build` -- allowed here, in tests only, as the
        // thing under test -- doesn't trip it. `decompile` itself contains
        // "compile" as a substring but is a single token, so it's fine.
        let src = include_str!("decompile.rs");
        let lines: Vec<&str> = src.lines().collect();
        let tests_start = lines
            .iter()
            .enumerate()
            .find(|(i, l)| l.trim() == "#[cfg(test)]" && lines.get(i + 1).is_some_and(|next| next.trim_start().starts_with("mod tests")))
            .map_or(lines.len(), |(i, _)| i);
        let code = &lines[..tests_start];
        for forbidden in ["compile", "lower_wat"] {
            let hit = code.iter().any(|l| {
                let l = l.trim_start();
                !l.starts_with("//") && l.split(|c: char| !c.is_alphanumeric() && c != '_').any(|tok| tok == forbidden)
            });
            assert!(!hit, "decompile.rs must not use {forbidden}");
        }
        assert!(!code.iter().any(|l| l.contains("use super::super")), "decompile.rs must not use super::super");
        // Denylisting "compile"/"lower_wat" only catches those two names.
        // An allowlist catches everything else too: every `crate::` path
        // above the test module must lead into `crate::ir` or
        // `crate::term`, whatever comes after -- `crate::proof`,
        // `crate::jit`, a future module, all rejected the same way.
        for l in code {
            let l = l.trim_start();
            if l.starts_with("//") {
                continue;
            }
            // Collapse whitespace so `crate :: compile` can't dodge the
            // `crate::` substring search below the way it dodges the
            // token-based denylist above. `pub(crate)` has no `::` after
            // `crate` even once collapsed, so it never matches.
            let compact: String = l.chars().filter(|c| !c.is_whitespace()).collect();
            // `decompile` sits directly under the crate root, so `super::`
            // reaches the same siblings `crate::` does.
            for prefix in ["crate::", "super::"] {
                let mut rest = compact.as_str();
                while let Some(i) = rest.find(prefix) {
                    let after = &rest[i + prefix.len()..];
                    let end = after.find(|c: char| !c.is_alphanumeric() && c != '_').unwrap_or(after.len());
                    let head = &after[..end];
                    assert!(head == "ir" || head == "term", "decompile.rs must not use {prefix}{head} (only ir and term are allowed)");
                    rest = &after[end..];
                }
            }
        }
    }

    use crate::ir::check;
    use std::collections::HashSet;

    const KINDS: [&str; 12] = [
        "swap arguments 0,1",
        "swap arguments 1,2",
        "swap environment slots",
        "swap branches",
        "shift a read up",
        "shift a read down",
        "shift an environment entry up",
        "shift an environment entry down",
        "change an operator",
        "retarget a combinator up",
        "retarget a combinator down",
        "retarget a Pap's root",
    ];
    /// The index into `KINDS` of "retarget a Pap's root". Handled outside
    /// `mutate` because it changes `Module::combinators`, not the node
    /// `mutate` is given -- a `MakePap` node names its *wrapper*, and the
    /// wrapper's `root` field lives one level away, in the combinator table.
    const PAP_ROOT_VARIANT: usize = 11;

    fn next_arith(op: PrimOp) -> PrimOp {
        use PrimOp::*;
        match op {
            Add => Sub,
            Sub => Mul,
            Mul => Div,
            Div => Mod,
            Mod => Add,
            other => other,
        }
    }

    fn next_cmp(op: PrimOp) -> PrimOp {
        use PrimOp::*;
        match op {
            Lt => Le,
            Le => Eq,
            Eq => Lt,
            other => other,
        }
    }

    fn swap_adjacent<T: PartialEq>(v: &mut [T], i: usize) -> bool {
        if i + 1 < v.len() && v[i] != v[i + 1] {
            v.swap(i, i + 1);
            true
        } else {
            false
        }
    }

    fn shift(r: &mut Read, up: bool) -> bool {
        let k = match r {
            Read::Param(k) | Read::Env(k) => k,
        };
        if up {
            *k += 1;
            true
        } else if *k > 0 {
            *k -= 1;
            true
        } else {
            false
        }
    }

    /// Moves index `i` to a neighbouring combinator that exists and is
    /// *different*. Retargeting to a structurally identical combinator
    /// would not change the meaning, so it is not a mutation.
    fn retarget(i: &mut usize, up: bool, combinators: &[Combinator]) -> bool {
        let j = if up { *i + 1 } else if *i > 0 { *i - 1 } else { return false };
        if j >= combinators.len() || combinators[j] == combinators[*i] {
            return false;
        }
        *i = j;
        true
    }

    /// Applies mutation `variant` (an index into `KINDS`) to `n`. Returns
    /// whether it applied and changed something.
    fn mutate(n: &mut Node, variant: usize, combinators: &[Combinator]) -> bool {
        fn args(n: &mut Node) -> Option<&mut Vec<Node>> {
            match n {
                Node::SelfCall { args, .. } | Node::CallKnown { args, .. } | Node::CallUnknown { args, .. } | Node::MakePap { args, .. } => Some(args),
                _ => None,
            }
        }
        fn env(n: &mut Node) -> Option<&mut Vec<Read>> {
            match n {
                Node::CallKnown { env, .. } | Node::MakeClosure { env, .. } => Some(env),
                Node::MakePap { root_env, .. } => Some(root_env),
                _ => None,
            }
        }
        match variant {
            0 | 1 => args(n).is_some_and(|a| swap_adjacent(a, variant)),
            2 => env(n).is_some_and(|e| swap_adjacent(e, 0)),
            3 => match n {
                Node::If { then, els, .. } if then != els => {
                    std::mem::swap(then, els);
                    true
                }
                _ => false,
            },
            4 | 5 => match n {
                Node::Read(r) => shift(r, variant == 4),
                _ => false,
            },
            // Slot 0 is always the capturing scope's highest-indexed
            // variable (see the corpus note in task-3-report.md), so
            // shifting it *up* never has headroom. Slot 0 shifting *down*
            // (variant 7) still exercises the "down" direction fine; the
            // "up" direction (variant 6) instead shifts the *last* slot,
            // which has headroom whenever the environment holds more than
            // one distinct free variable.
            6 => env(n).and_then(|e| e.last_mut()).is_some_and(|r| shift(r, true)),
            7 => env(n).and_then(|e| e.first_mut()).is_some_and(|r| shift(r, false)),
            8 => match n {
                Node::Arith(op, ..) => {
                    *op = next_arith(*op);
                    true
                }
                Node::If { cmp, .. } => {
                    *cmp = next_cmp(*cmp);
                    true
                }
                _ => false,
            },
            9 | 10 => match n {
                Node::CallKnown { f, .. } | Node::MakeClosure { f, .. } => retarget(f, variant == 9, combinators),
                Node::MakePap { wrapper, .. } => retarget(wrapper, variant == 9, combinators),
                _ => false,
            },
            _ => false,
        }
    }

    fn preorder_len(n: &Node) -> usize {
        1 + n.children().into_iter().map(preorder_len).sum::<usize>()
    }

    /// The `k`-th node of `n` in preorder (`k` counts down to 0).
    fn nth_mut<'a>(n: &'a mut Node, k: &mut usize) -> Option<&'a mut Node> {
        if *k == 0 {
            return Some(n);
        }
        *k -= 1;
        for c in n.children_mut() {
            if let Some(found) = nth_mut(c, k) {
                return Some(found);
            }
        }
        None
    }

    /// Like `nth_mut`, read-only: used to find the `MakePap` at node `k`
    /// without borrowing `mutant.funcs_mut()`, which would collide with the
    /// separate mutable borrow of `mutant.combinators` that
    /// `retarget_pap_root` needs.
    fn nth<'a>(n: &'a Node, k: &mut usize) -> Option<&'a Node> {
        if *k == 0 {
            return Some(n);
        }
        *k -= 1;
        for c in n.children() {
            if let Some(found) = nth(c, k) {
                return Some(found);
            }
        }
        None
    }

    /// Moves a `MakePap` wrapper's `Combinator::Pap.root` to a neighbouring
    /// combinator, the same up-then-down, skip-if-identical shape as
    /// `retarget`. `root` names a *lambda*, not the wrapper itself, so this
    /// mutation is a different injectivity check from variants 9-10 (which
    /// retarget the wrapper index a `MakeClosure`/`CallKnown`/`MakePap`
    /// node holds): it catches a decompiler that reads `combinators[wrapper]`
    /// correctly but rebuilds the wrong lambda for its `root`. An
    /// out-of-range or non-`Lifted` candidate is left for `check` to reject,
    /// same as every other mutation here.
    fn retarget_pap_root(m: &mut Module, wrapper: usize) -> bool {
        let Some(Combinator::Pap { root, .. }) = m.combinators.get(wrapper) else {
            return false;
        };
        let root = *root;
        // Try down first: a Pap wrapper is built right after its root (see
        // `compile::build`), so `root + 1` is usually the wrapper itself --
        // not `Lifted`, so `check` always rejects it -- while `root - 1` is
        // usually a distinct lambda and often well-formed.
        for cand in [root.checked_sub(1), root.checked_add(1)].into_iter().flatten() {
            if cand >= m.combinators.len() || m.combinators[cand] == m.combinators[root] {
                continue;
            }
            let Combinator::Pap { root: r, .. } = &mut m.combinators[wrapper] else { unreachable!() };
            *r = cand;
            return true;
        }
        false
    }

    #[test]
    fn every_single_point_mutation_of_a_built_module_is_rejected() {
        // For every real module, every node, and every mutation kind that
        // applies and leaves the module well-formed (so `lower` would accept
        // it), the mutant must NOT decompile to the source hash. If one did,
        // the gate would accept a module that means something else.
        let mut applied = 0usize;
        let mut kinds_seen = HashSet::new();
        for (name, s, h) in crate::test_corpus::terms() {
            let m = crate::compile::build(&s, h).unwrap();
            for fi in 0..m.funcs().count() {
                let nodes = preorder_len(&m.funcs().nth(fi).unwrap().body);
                for k in 0..nodes {
                    for (variant, kind) in KINDS.iter().enumerate() {
                        let mut mutant = m.clone();
                        let changed = if variant == PAP_ROOT_VARIANT {
                            let mut kk = k;
                            match nth(&m.funcs().nth(fi).unwrap().body, &mut kk) {
                                Some(Node::MakePap { wrapper, .. }) => retarget_pap_root(&mut mutant, *wrapper),
                                _ => false,
                            }
                        } else {
                            let mut fs = mutant.funcs_mut();
                            let mut kk = k;
                            let node = nth_mut(&mut fs[fi].body, &mut kk).unwrap();
                            mutate(node, variant, &m.combinators)
                        };
                        if !changed || mutant == m || check(&mutant).is_err() {
                            continue;
                        }
                        applied += 1;
                        kinds_seen.insert(*kind);
                        assert_ne!(
                            decompile(&mutant, &mut TermStore::new()),
                            Some(h),
                            "{name}: `{kind}` at node {k} of function {fi} still decompiles to the source hash"
                        );
                    }
                }
            }
        }
        // Not vacuous: many mutants were actually tried, of every kind.
        assert!(applied >= 200, "only {applied} well-formed mutants were tried");
        for kind in KINDS {
            assert!(kinds_seen.contains(kind), "no well-formed mutant of kind `{kind}` was produced");
        }
    }

    #[test]
    fn flipping_a_self_calls_tail_flag_keeps_the_meaning() {
        // Field-parity class 2: `tail` picks a loop or a call, and both are
        // correct. The decompiler must therefore not reject the flip, or
        // the gate would reject correct code.
        let mut flipped = 0;
        for (name, s, h) in crate::test_corpus::terms() {
            let mut m = crate::compile::build(&s, h).unwrap();
            fn untail(n: &mut Node, count: &mut usize) {
                if let Node::SelfCall { tail, .. } = n
                    && *tail
                {
                    *tail = false;
                    *count += 1;
                }
                for c in n.children_mut() {
                    untail(c, count);
                }
            }
            for f in m.funcs_mut() {
                untail(&mut f.body, &mut flipped);
            }
            check(&m).unwrap();
            assert_eq!(decompile(&m, &mut TermStore::new()), Some(h), "{name}");
        }
        assert!(flipped > 0);
    }
}
