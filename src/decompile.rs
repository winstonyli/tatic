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
#![cfg_attr(not(test), allow(dead_code))] // wired into try_compile in Task 2

use hashbrown::HashMap;

use crate::ir::{Combinator, Func, Module, Node, Read};
use crate::term::{Hash, TermStore};

/// The term `m` implements, built into `s`. `None` if `m` refers to
/// something that does not exist: a combinator index out of range, a read
/// out of range, a self-call in a non-recursive function, or a
/// partial-application wrapper that isn't one. `ir::check` rejects all of
/// these first, but the decompiler derives what it needs itself instead of
/// trusting that.
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
    fn the_decompiler_imports_nothing_from_the_compiler() {
        // The whole point of the check is that a bug in `compile.rs`'s
        // helpers cannot be mirrored here. Enforced mechanically.
        let src = include_str!("decompile.rs");
        for forbidden in ["crate::compile", "crate::lower_wat", "use super::super"] {
            let hits = src.lines().filter(|l| l.contains(forbidden) && !l.contains("forbidden") && !l.trim_start().starts_with("//")).filter(|l| !l.contains("crate::compile::build")).count();
            assert_eq!(hits, 0, "decompile.rs must not use {forbidden}");
        }
    }
}
