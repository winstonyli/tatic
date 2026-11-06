//! The memos over the hash-consed spaces (bit-vector design doc sections 60 and 62): `instantiate_n`, `shift_child`,
//! `whnf`, head normal forms and `nf`, keyed by node (`Spaces::key`) and kept in `Spaces::memos` until the region
//! closes. A node is one term, so a memo entry serves every place the term occurs.
//!
//! A walk's memo (`inst`, `shifts`, `InferCache`'s `lows` and `types`, `abstract_frees_in`'s) stores only shared nodes
//! (`Spaces::shared`, two or more parents). An unshared node is reached only through its one parent, so a repeated walk
//! stops at the parent's entry first: its own entry would almost never be read (77% of `inst`'s entries took 14 of
//! 148,047 hits in rule 33's check at n=64; doc section "Why `inst` has many entries per node"). `whnf`, `hnf` and
//! `nf` serve calls on any term, not one walk, and `uses`' `bounds` is asked again per `m`, so they keep every node.
use super::*;

/// Terms larger than this many nodes (counted once per node below the roots) are checked on one big stack segment
/// (`check_in`). This crate's unit tests take that path for every input; other crates' tests see the real limit.
const LARGE: usize = if cfg!(test) { 0 } else { 3000 };

/// Whether the terms reachable from `roots` have more than `limit` distinct nodes below them.
fn exceeds(s: &Spaces, roots: &[&Expr], limit: usize) -> bool {
    // The walk stops once `seen` holds `limit + 1` keys, so it never grows past this.
    let mut seen: IdSet<Key> = IdSet::with_capacity_and_hasher(limit + 1, Default::default());
    let mut stack: Vec<Expr> = roots.iter().map(|&e| *e).collect();
    while let Some(e) = stack.pop() {
        let mut over = false;
        s.node(&e).for_kids(|p, _| {
            if !over && seen.insert(s.key(p)) {
                over = seen.len() > limit;
                stack.push(*p);
            }
        });
        if over {
            return true;
        }
    }
    limit == 0 && !roots.is_empty()
}

/// Whether `check_in`'s term and claim are large, so that it runs them on one big stack segment (`on_segment`).
pub fn large(s: &Spaces, e: &Expr, expected: &Expr) -> bool {
    exceeds(s, &[e, expected], LARGE)
}

/// Whether `x` mentions a loose `Var` in `[d, d + m)`, i.e. whether instantiating `m` arguments
/// at depth `d` can put any of them in. When it cannot, the result is `x` shifted down by `m`
/// above `d + m`, whatever the arguments are. The node remembers its last answer
/// ([`Spaces::uses_slot`]). Its misses go to the memos' `bounds` on the node's lowest loose
/// variable from `d`, which one (node, depth) entry answers for every `m` outside them; a walk
/// that still stops at its first hit narrows them (doc section "The slot in front of bounds").
pub fn uses(s: &Spaces, x: &Expr, d: u32, m: u32) -> bool {
    let loose = s.loose(x);
    if loose <= d {
        return false;
    }
    let n = s.node(x);
    if let Node::Var(k) = n {
        return k < d + m;
    }
    if let Some(r) = s.uses_slot(x, d, m) {
        return r;
    }
    // `lo <= the lowest loose variable from d <= hi`. `loose` bounds it from above unless it
    // saturated.
    let key = (s.key(x), d);
    let (lo, hi) = s
        .memos
        .borrow()
        .bounds
        .get(&key)
        .copied()
        .unwrap_or((0, if loose == u32::MAX { u32::MAX } else { loose - 1 - d }));
    let r = if hi < m {
        true
    } else if lo >= m {
        false
    } else {
        let r = grow(|| {
            let mut found = false;
            n.for_kids(|c, under| found = found || uses(s, c, d + under as u32, m));
            found
        });
        let b = if r { (lo, m - 1) } else { (m, hi) };
        s.memos.borrow_mut().bounds.insert(key, b);
        r
    };
    s.set_uses_slot(x, d, m, r);
    r
}

/// The smallest loose `Var` index of `x` seen from `d` binders inside it, i.e. among `x`'s loose
/// variables `k >= d`, the least `k - d`; `u32::MAX` when there is none. Memoised in `memo` by
/// (node, `d`) for shared nodes (see [`hc`](self)); its one caller, `memo_context`, asks only of
/// shared ones. A shared node's answer from 0, `l`, also answers every `d <= l` as `l - d`, so
/// a node reached at many depths, like a shared term under a growing stack of binders it
/// doesn't use, is walked once rather than once per depth; only depths past `l` get entries
/// of their own.
pub(super) fn lowest_loose(s: &Spaces, x: &Expr, d: u32, memo: &mut IdMap<(Key, u32), u32>) -> u32 {
    if s.loose(x) <= d {
        return u32::MAX;
    }
    let n = s.node(x);
    if let Node::Var(k) = n {
        return k - d;
    }
    let shared = s.shared(x);
    if shared && d > 0 {
        let l = lowest_loose(s, x, 0, memo);
        if l >= d {
            return l - d;
        }
    }
    let key = (s.key(x), d);
    if shared && let Some(&r) = memo.get(&key) {
        return r;
    }
    let r = grow(|| {
        let mut low = u32::MAX;
        n.for_kids(|c, under| low = low.min(lowest_loose(s, c, d + under as u32, memo)));
        low
    });
    if shared {
        memo.insert(key, r);
    }
    r
}

/// An id for the argument list: the node's key for one argument (`LIST_BIT` clear), `LIST_BIT | n` for the `n`-th
/// list of several.
pub fn args_id(s: &Spaces, args: &[&Expr]) -> Aid {
    if let [a] = args {
        return s.key(a);
    }
    // The keys go in a stack buffer when they fit; the set is only allocated for a new list.
    let mut buf = [0u32; 8];
    let heap: Vec<u32>;
    let keys: &[u32] = if args.len() <= buf.len() {
        buf.iter_mut().zip(args).for_each(|(k, a)| *k = s.key(a));
        &buf[..args.len()]
    } else {
        heap = args.iter().map(|a| s.key(a)).collect();
        &heap
    };
    let mut m = s.memos.borrow_mut();
    if let Some(&n) = m.arg_sets.get(keys) {
        return n;
    }
    let n = m.arg_sets.len() as u32;
    assert!(n < LIST_BIT, "argument lists ran out of ids");
    m.arg_sets.insert(keys.to_vec(), LIST_BIT | n);
    LIST_BIT | n
}

/// Whether `x` is too small for the instantiation memo to pay: at most two levels above its
/// leaves. Rebuilding such a node is a few node-table probes; its memo entry cost a probe and an
/// insert for a 36% hit rate (one level), and the cutoff at two beat one, three and four (doc
/// section "Small nodes skip the instantiation memo").
pub fn low(s: &Spaces, x: &Expr) -> bool {
    s.height(x) <= 2
}

pub fn inst_get(s: &Spaces, x: &Expr, aid: Aid, d: u32) -> Option<Expr> {
    s.memos.borrow().inst.get(&(s.key(x), aid, d)).map(|r| s.expr_of(r))
}

pub fn inst_put(s: &Spaces, x: &Expr, aid: Aid, d: u32, r: &Expr) {
    s.memos.borrow_mut().inst.insert((s.key(x), aid, d), s.key(r));
}

/// `x`'s weak head normal form, if the memos have it. `whnf` reads no context, so an answer holds for the whole
/// region, across `def_eq` calls (doc section "Why the table lookups stay").
pub fn whnf_get(s: &Spaces, x: &Expr) -> Option<Expr> {
    s.memos.borrow().whnf.get(&s.key(x)).map(|r| s.expr_of(r))
}

pub fn whnf_put(s: &Spaces, x: &Expr, r: &Expr) {
    s.memos.borrow_mut().whnf.insert(s.key(x), s.key(r));
}

pub fn nf_get(s: &Spaces, x: &Expr) -> Option<Expr> {
    s.memos.borrow().nf.get(&s.key(x)).map(|r| s.expr_of(r))
}

pub fn nf_put(s: &Spaces, x: &Expr, r: &Expr) {
    s.memos.borrow_mut().nf.insert(s.key(x), s.key(r));
}

/// Closed node -> its head normal form; see `hnf_rc`.
pub fn hnf_get(s: &Spaces, x: &Expr) -> Option<Expr> {
    s.memos.borrow().hnf.get(&s.key(x)).map(|r| s.expr_of(r))
}

pub fn hnf_put(s: &Spaces, x: &Expr, r: &Expr) {
    s.memos.borrow_mut().hnf.insert(s.key(x), s.key(r));
}

/// Application -> its spine's head and closed prefix; see `spine`.
pub fn spine_get(s: &Spaces, x: &Expr) -> Option<(Expr, Option<Expr>)> {
    s.memos.borrow().spine.get(&s.key(x)).map(|&(h, p)| (s.expr_of(&h), p.map(|p| s.expr_of(&p))))
}

pub fn spine_put(s: &Spaces, x: &Expr, (h, p): (Expr, Option<Expr>)) {
    s.memos.borrow_mut().spine.insert(s.key(x), (s.key(&h), p.map(|p| s.key(&p))));
}

pub fn shift_get(s: &Spaces, x: &Expr, cutoff: u32, amount: i32) -> Option<Expr> {
    s.memos.borrow().shifts.get(&(s.key(x), cutoff, amount)).map(|r| s.expr_of(r))
}

pub fn shift_put(s: &Spaces, x: &Expr, cutoff: u32, amount: i32, r: &Expr) {
    s.memos.borrow_mut().shifts.insert((s.key(x), cutoff, amount), s.key(r));
}
