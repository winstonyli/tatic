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

use crate::jit::ir::{Combinator, Func, Module, Node, Read};
use crate::lang::term::{Hash, TermStore};

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
    /// closure. `Rec` is outermost, as `shape::peel` expects.
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
            Node::SelfCall { args } => {
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
mod tests;
