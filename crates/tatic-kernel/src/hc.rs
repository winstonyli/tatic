//! The memos over the hash-consed spaces (bit-vector design doc sections 60 and 62): `instantiate_n`, `shift_child`,
//! `whnf`, head normal forms and `nf`, keyed by node (`Spaces::key`) and kept in `Spaces::memos` until the region
//! closes. A node is one term, so a memo entry serves every place the term occurs.
//!
//! A walk's memo (`inst`, `InferCache`'s `lows` and `types`, `abstract_frees_in`'s) stores only shared nodes
//! (`Spaces::shared`, two or more parents). An unshared node is reached only through its one parent, so a repeated walk
//! stops at the parent's entry first: its own entry would almost never be read (77% of `inst`'s entries took 14 of
//! 148,047 hits in rule 33's check at n=64; doc section "Why `inst` has many entries per node"). `whnf`, `hnf` and
//! `nf` serve calls on any term, not one walk, so they keep every node.
//! `shifts` keeps every node too: shifts start from call roots with no entry of their own, and the gate's check
//! reached the same unshared program suffixes from such roots at every step, 4x the work per doubling of the tree (doc
//! 15, "Why the check grew 4x per doubling").
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

/// Whether `check_in`'s term and claim are large, so that it runs them on one big stack segment (`on_segment`) unless the thread has the room.
pub fn large(s: &Spaces, e: &Expr, expected: &Expr) -> bool {
    exceeds(s, &[e, expected], LARGE)
}

/// Whether `x` mentions a loose `Var` in `[d, d + m)`, i.e. whether instantiating `m` arguments
/// at depth `d` can put any of them in. When it cannot, the result is `x` shifted down by `m`
/// above `d + m`, whatever the arguments are. The node keeps one bounds slot
/// ([`Spaces::bounds_slot`]): `lo <= the lowest loose variable from d <= hi`, for the last depth `d` asked.
/// A query with `hi < m` or `lo >= m` is answered from it, whatever `m`; any other walks the children
/// and narrows the bounds to what the answer shows.
pub fn uses(s: &Spaces, x: &Expr, d: u32, m: u32) -> bool {
    let loose = s.loose(x);
    if loose <= d {
        return false;
    }
    let n = s.node(x);
    if let Node::Var(k) = n {
        return k < d + m;
    }
    // `loose` bounds the lowest loose variable from above unless it saturated.
    let (lo, hi) = s.bounds_slot(x, d).unwrap_or((0, if loose == u32::MAX { u32::MAX } else { loose - 1 - d }));
    if hi < m {
        true
    } else if lo >= m {
        false
    } else {
        let r = grow(|| {
            let mut found = false;
            n.for_kids(|c, under| found = found || uses(s, c, d + under as u32, m));
            found
        });
        let (lo, hi) = if r { (lo, m - 1) } else { (m, hi) };
        s.set_bounds_slot(x, d, lo, hi);
        r
    }
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

/// Whether `x` is too small for the instantiation memo to pay: at most two levels above its
/// leaves. Rebuilding such a node is a few node-table probes; its memo entry cost a probe and an
/// insert for a 36% hit rate (one level), and the cutoff at two beat one, three and four (doc
/// section "Small nodes skip the instantiation memo").
pub fn low(s: &Spaces, x: &Expr) -> bool {
    s.height(x) <= 2
}

/// The small id of an `instantiate_n` argument list, by the keys of its arguments in order; the same list gets the same
/// id for the rest of the region. A known list allocates nothing (the lookup borrows a `&[u32]`), and a list of up to
/// eight arguments is keyed from a stack buffer.
pub fn inst_args_id(s: &Spaces, args: &[&Expr]) -> u32 {
    let mut buf = [0u32; 8];
    let heap: Vec<u32>;
    let keys: &[u32] = if args.len() <= buf.len() {
        for (b, a) in buf.iter_mut().zip(args) {
            *b = s.key(a);
        }
        &buf[..args.len()]
    } else {
        heap = args.iter().map(|a| s.key(a)).collect();
        &heap
    };
    let mut m = s.memos.borrow_mut();
    if let Some(&id) = m.inst_args.get(keys) {
        return id;
    }
    let id = m.inst_args.len() as u32;
    m.inst_args.insert(keys.into(), id);
    id
}

pub fn inst_get(s: &Spaces, x: &Expr, d: u32, args: u32) -> Option<Expr> {
    s.memos.borrow().inst.get(&(s.key(x), d, args)).map(|r| s.expr_of(r))
}

pub fn inst_put(s: &Spaces, x: &Expr, d: u32, args: u32, r: &Expr) {
    s.memos.borrow_mut().inst.insert((s.key(x), d, args), s.key(r));
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
