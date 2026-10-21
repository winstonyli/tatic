//! The id arena (spec `docs/superpowers/specs/2026-10-14-id-arena-spec.md`, "Design"). A term is a 32-bit [`Ref`] into
//! one of two per-thread spaces, both hash-consed:
//! - the *persistent* space only grows;
//! - the *region* is a check's working memory, opened by the outermost `scoped` and freed in bulk when it closes.
//!
//! A persistent node has only persistent children. While a region is open, `persist` copies region nodes out bottom-up
//! and records each copy's region *twin*. Reading a persistent `Ref` at or above `w` (the persistent length when the
//! region opened) gives its twin. So no two `Ref`s that callers see name the same term (Invariant I), and `==` on
//! resolved `Ref`s is structural equality.
//!
//! The one `unsafe` contract is local to this file: `inner()`'s `&mut` lives within one method body, never across a
//! call that can reach `inner` again (`persist` drops it before recursing), and no method returns a reference into
//! the vectors. Reads return copies, so a vector that grows never leaves a borrow dangling.

use super::Node;
use std::cell::{RefCell, UnsafeCell};
use std::hash::BuildHasherDefault;

/// A node in one of the two spaces: bit 31 set for the region, bits 0-29 the index into that space.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(crate) struct Ref(pub(crate) u32);

const REGION_BIT: u32 = 1 << 31;
const INDEX_MASK: u32 = (1 << 30) - 1;
/// Set in an argument-list id (`hc::args_id`) and clear in every `Ref`, so the two never collide as `Memos::inst` keys.
pub(crate) const LIST_BIT: u32 = 1 << 30;

impl Ref {
    fn new(region: bool, index: usize) -> Ref {
        assert!(index <= INDEX_MASK as usize, "{} space full", if region { "region" } else { "persistent" });
        Ref(if region { REGION_BIT } else { 0 } | index as u32)
    }
    #[inline(always)]
    pub(crate) fn in_region(self) -> bool {
        self.0 & REGION_BIT != 0
    }
    #[inline(always)]
    fn index(self) -> usize {
        (self.0 & INDEX_MASK) as usize
    }
}

/// Hashes the integers a memo key is made of by multiply and rotate, with no per-map seed: the keys are the kernel's own
/// ids, not attacker-chosen input (formerly `PtrHasher`; bit-vector design doc §47).
#[derive(Default, Clone, Copy)]
pub(crate) struct IdHasher(u64);
impl std::hash::Hasher for IdHasher {
    fn finish(&self) -> u64 {
        self.0.rotate_left(26)
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.write_u64(*b as u64);
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    fn write_u32(&mut self, x: u32) {
        self.write_u64(x as u64);
    }
    fn write_usize(&mut self, x: usize) {
        self.write_u64(x as u64);
    }
}
pub(crate) type IdMap<K, V> = hashbrown::HashMap<K, V, BuildHasherDefault<IdHasher>>;
pub(crate) type IdSet<K> = hashbrown::HashSet<K, BuildHasherDefault<IdHasher>>;
const H: BuildHasherDefault<IdHasher> = BuildHasherDefault::new();

/// A node's 32-bit hash: the tag and leaf, then each child's `Ref`, folded by multiply and rotate; the top half.
fn hash(n: &Node<Ref>) -> u32 {
    const K: u64 = 0x517c_c1b7_2722_0a95;
    let (tag, leaf) = n.tag_leaf();
    let mut h = ((tag as u64) << 32 | leaf as u64).wrapping_mul(K);
    n.for_kids(|c, _| h = (h.rotate_left(5) ^ c.0 as u64).wrapping_mul(K));
    (h >> 32) as u32
}

/// The stored 32-bit hash spread to 64 for hashbrown, which takes its 7-bit tag from the top bits: zero-extended, every
/// entry would get tag 0 and every probe would read nodes (spec, "Kernel internals").
#[inline(always)]
fn spread(h: u32) -> u64 {
    (h as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

/// Empties `v`, and gives its memory back when it held under a quarter of its capacity, so a small region after a large
/// one doesn't pay for the large one's capacity (hashbrown's `clear` costs time in the capacity; spec, "Kernel
/// internals").
fn reset_vec<T>(v: &mut Vec<T>) {
    let used = v.len();
    v.clear();
    if used < v.capacity() / 4 {
        v.shrink_to(used);
    }
}
fn reset_map<K: Eq + std::hash::Hash, V>(m: &mut IdMap<K, V>) {
    let used = m.len();
    m.clear();
    if used < m.capacity() / 4 {
        m.shrink_to(used);
    }
}

/// One space: its nodes, their side arrays and its table.
struct Space {
    nodes: Vec<Node<Ref>>,
    /// Per node, as `Expr::loose` and `Expr::free`.
    loose: Vec<u32>,
    free: Vec<u32>,
    /// Per node, the `hc::uses` slot (0: empty).
    uses: Vec<u32>,
    /// Per node, the nodes built over it, saturating at 2 (`Expr::shared`).
    parents: Vec<u8>,
    /// Per node, its height (a leaf 0), saturating: what `hc::low` asks without a walk.
    height: Vec<u8>,
    /// Each node's hash and `Ref`: 8 bytes an entry.
    table: hashbrown::HashTable<(u32, Ref)>,
}

impl Space {
    const fn new() -> Space {
        Space { nodes: Vec::new(), loose: Vec::new(), free: Vec::new(), uses: Vec::new(), parents: Vec::new(), height: Vec::new(), table: hashbrown::HashTable::new() }
    }
    fn find(&self, h: u32, n: &Node<Ref>) -> Option<Ref> {
        self.table.find(spread(h), |&(g, r)| g == h && self.nodes[r.index()] == *n).map(|&(_, r)| r)
    }
    fn push(&mut self, region: bool, h: u32, n: Node<Ref>, (loose, free): (u32, u32), parents: u8, height: u8) -> Ref {
        let r = Ref::new(region, self.nodes.len());
        self.nodes.push(n);
        self.loose.push(loose);
        self.free.push(free);
        self.uses.push(0);
        self.parents.push(parents);
        self.height.push(height);
        self.table.insert_unique(spread(h), (h, r), |&(g, _)| spread(g));
        r
    }
    fn clear(&mut self) {
        reset_vec(&mut self.nodes);
        reset_vec(&mut self.loose);
        reset_vec(&mut self.free);
        reset_vec(&mut self.uses);
        reset_vec(&mut self.parents);
        reset_vec(&mut self.height);
        let used = self.table.len();
        self.table.clear();
        if used < self.table.capacity() / 4 {
            self.table.shrink_to(used, |&(g, _)| spread(g));
        }
    }
}

/// The region's memos, keyed by resolved `Ref` bits and emptied when it closes (they were `hc::Table`'s and
/// `ReductionCache`'s). Entries made with no region open name persistent nodes and stay valid until the next close.
pub(crate) struct Memos {
    /// (node, argument-list id, depth) -> its instantiation.
    pub(crate) inst: IdMap<(u32, u32, u32), u32>,
    /// (node, cutoff, amount) -> it shifted.
    pub(crate) shifts: IdMap<(u32, u32, i32), u32>,
    /// Node -> its weak head normal form.
    pub(crate) whnf: IdMap<u32, u32>,
    /// Closed node -> its head normal form.
    pub(crate) hnf: IdMap<u32, u32>,
    /// Node -> its normal form.
    pub(crate) nf: IdMap<u32, u32>,
    /// Application -> its spine's head and its longest proper prefix with no loose variable (`kernel::spine`).
    pub(crate) spine: IdMap<u32, (u32, Option<u32>)>,
    /// Argument lists of two or more nodes -> their id (`LIST_BIT | n`).
    pub(crate) arg_sets: IdMap<Vec<u32>, u32>,
    /// (node, depth) -> bounds `(lo, hi)` on its lowest loose variable from that depth (`hc::uses`).
    pub(crate) bounds: IdMap<(u32, u32), (u32, u32)>,
}

impl Memos {
    const fn new() -> Memos {
        Memos {
            inst: IdMap::with_hasher(H),
            shifts: IdMap::with_hasher(H),
            whnf: IdMap::with_hasher(H),
            hnf: IdMap::with_hasher(H),
            nf: IdMap::with_hasher(H),
            spine: IdMap::with_hasher(H),
            arg_sets: IdMap::with_hasher(H),
            bounds: IdMap::with_hasher(H),
        }
    }
    fn clear(&mut self) {
        reset_map(&mut self.inst);
        reset_map(&mut self.shifts);
        reset_map(&mut self.whnf);
        reset_map(&mut self.hnf);
        reset_map(&mut self.nf);
        reset_map(&mut self.spine);
        reset_map(&mut self.arg_sets);
        reset_map(&mut self.bounds);
    }
}

struct Inner {
    persistent: Space,
    region: Space,
    /// The open region's generation; 0 while none is open. Never reused.
    epoch: u32,
    next_epoch: u32,
    /// The persistent length when the region opened; `u32::MAX` while none is open, so every persistent `Ref` is below.
    w: u32,
    /// Region index -> its persistent copy's `Ref`, `u32::MAX` for none: `persist`'s memo.
    copies: Vec<u32>,
    /// Persistent index - `w` -> the region node it was copied from.
    twins: Vec<Ref>,
}

/// This thread's two spaces and the region's memos.
pub(crate) struct Spaces {
    inner: UnsafeCell<Inner>,
    pub(crate) memos: RefCell<Memos>,
}

impl Spaces {
    pub(crate) const fn new() -> Spaces {
        Spaces {
            inner: UnsafeCell::new(Inner {
                persistent: Space::new(),
                region: Space::new(),
                epoch: 0,
                next_epoch: 1,
                w: u32::MAX,
                copies: Vec::new(),
                twins: Vec::new(),
            }),
            memos: RefCell::new(Memos::new()),
        }
    }

    #[inline(always)]
    fn get(&self) -> &Inner {
        // SAFETY: see the module doc; no `&mut` from `inner()` is live across a call to this.
        unsafe { &*self.inner.get() }
    }

    #[allow(clippy::mut_from_ref)]
    #[inline(always)]
    fn inner(&self) -> &mut Inner {
        // SAFETY: see the module doc.
        unsafe { &mut *self.inner.get() }
    }

    #[inline(always)]
    fn space(&self, r: Ref) -> &Space {
        let i = self.get();
        if r.in_region() { &i.region } else { &i.persistent }
    }

    /// The open region's generation, 0 while none is open.
    #[inline(always)]
    pub(crate) fn epoch(&self) -> u32 {
        self.get().epoch
    }

    /// The `Ref` that a handle made in generation `epoch` names now. A region `Ref` must come from the open region, or the
    /// handle is dead. A persistent one at or above `w` reads as its region twin (Invariant R).
    #[inline(always)]
    pub(crate) fn resolve(&self, r: Ref, epoch: u32) -> Ref {
        let i = self.get();
        if r.in_region() {
            assert!(epoch == i.epoch && epoch != 0, "dead handle: a term used after the scope it was built in closed (persist it, or return it from `scoped`)");
            r
        } else if r.0 >= i.w {
            i.twins[(r.0 - i.w) as usize]
        } else {
            r
        }
    }

    /// Whether [`resolve`](Spaces::resolve) would succeed.
    #[inline(always)]
    pub(crate) fn live(&self, r: Ref, epoch: u32) -> bool {
        !r.in_region() || (epoch == self.get().epoch && epoch != 0)
    }

    /// The node `r` (resolved) names.
    #[inline(always)]
    pub(crate) fn node_at(&self, r: Ref) -> Node<Ref> {
        self.space(r).nodes[r.index()]
    }
    #[inline(always)]
    pub(crate) fn loose_at(&self, r: Ref) -> u32 {
        self.space(r).loose[r.index()]
    }
    #[inline(always)]
    pub(crate) fn free_at(&self, r: Ref) -> u32 {
        self.space(r).free[r.index()]
    }
    #[inline(always)]
    pub(crate) fn parents_at(&self, r: Ref) -> u8 {
        self.space(r).parents[r.index()]
    }
    #[inline(always)]
    pub(crate) fn height_at(&self, r: Ref) -> u8 {
        self.space(r).height[r.index()]
    }
    #[inline(always)]
    pub(crate) fn uses_at(&self, r: Ref) -> u32 {
        self.space(r).uses[r.index()]
    }
    #[inline(always)]
    pub(crate) fn set_uses_at(&self, r: Ref, v: u32) {
        let i = self.inner();
        let s = if r.in_region() { &mut i.region } else { &mut i.persistent };
        s.uses[r.index()] = v;
    }

    /// The node `n` over resolved children. If all its children are persistent, it is looked up in the persistent space
    /// first, taking only a hit below `w` (one at or above is a copy, whose twin the region lookup finds). Then it is found
    /// in the region or built there, without the search when a region child has no parent yet. With no region open, it is found or built in the persistent space.
    pub(crate) fn build(&self, n: Node<Ref>) -> Ref {
        let h = hash(&n);
        let i = self.inner();
        let (mut persistent_kids, mut fresh_kid) = (true, false);
        n.for_kids(|c, _| {
            persistent_kids &= !c.in_region();
            fresh_kid |= c.in_region() && i.region.parents[c.index()] == 0;
        });
        if persistent_kids
            && let Some(r) = i.persistent.find(h, &n)
            && r.0 < i.w
        {
            return r;
        }
        let in_region = i.epoch != 0;
        debug_assert!(in_region || persistent_kids, "a region child with no region open");
        // A region child with no parent yet means no node over it exists: `parents` rises only when a node is pushed, and
        // persistent nodes have no region children. So the lookup, a cache miss, is skipped (a quarter of all builds;
        // docs/tier-cycle.md, "Skipping the lookup that must miss").
        debug_assert!(!fresh_kid || i.region.find(h, &n).is_none(), "a node over a parentless child already exists");
        if in_region && !fresh_kid && let Some(r) = i.region.find(h, &n) {
            return r;
        }
        let ranges = {
            let (p, g) = (&i.persistent, &i.region);
            let at = |c: &Ref| if c.in_region() { g } else { p };
            n.ranges(|c| at(c).loose[c.index()], |c| at(c).free[c.index()])
        };
        let height = {
            let (p, g) = (&i.persistent, &i.region);
            let mut height = 0u8;
            n.for_kids(|c, _| height = height.max((if c.in_region() { g } else { p }).height[c.index()].saturating_add(1)));
            height
        };
        n.for_kids(|c, _| {
            let s = if c.in_region() { &mut i.region } else { &mut i.persistent };
            let p = &mut s.parents[c.index()];
            *p = p.saturating_add(1).min(2);
        });
        if in_region { i.region.push(true, h, n, ranges, 0, height) } else { i.persistent.push(false, h, n, ranges, 0, height) }
    }

    /// `r` (resolved) as a persistent `Ref`. The region nodes reachable from it are copied out bottom-up, each once per
    /// region (`copies`), and every copy records its twin. The identity on a persistent `r`. The region stays usable.
    pub(crate) fn persist(&self, r: Ref) -> Ref {
        if !r.in_region() {
            return r;
        }
        let k = r.index();
        let n = {
            let i = self.inner();
            if let Some(&p) = i.copies.get(k)
                && p != u32::MAX
            {
                return Ref(p);
            }
            i.region.nodes[k]
        };
        let m = super::grow(|| n.map_kids(|c, _| self.persist(c)));
        let i = self.inner();
        let h = hash(&m);
        debug_assert!(i.persistent.find(h, &m).is_none(), "persist met a copy it did not make (Invariant I)");
        let p = i.persistent.push(false, h, m, (i.region.loose[k], i.region.free[k]), i.region.parents[k], i.region.height[k]);
        i.twins.push(r);
        debug_assert_eq!(i.w as usize + i.twins.len(), i.persistent.nodes.len());
        if i.copies.len() <= k {
            i.copies.resize(i.region.nodes.len(), u32::MAX);
        }
        i.copies[k] = p.0;
        p
    }

    /// Opens a region unless one is open; true when this call opened it.
    pub(crate) fn open(&self) -> bool {
        let i = self.inner();
        if i.epoch != 0 {
            return false;
        }
        i.epoch = i.next_epoch;
        i.next_epoch = i.next_epoch.checked_add(1).expect("region generations ran out");
        i.w = i.persistent.nodes.len() as u32;
        true
    }

    /// Closes the open region: its nodes, `copies`, twins and memos are emptied, and every handle into it is dead.
    pub(crate) fn close(&self) {
        let i = self.inner();
        i.epoch = 0;
        i.w = u32::MAX;
        i.region.clear();
        reset_vec(&mut i.copies);
        reset_vec(&mut i.twins);
        self.memos.borrow_mut().clear();
    }

    #[cfg(test)]
    fn persistent_len(&self) -> usize {
        self.get().persistent.nodes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::super::Node::*;
    use super::*;

    #[test]
    fn a_stored_node_is_24_bytes() {
        assert_eq!(std::mem::size_of::<Node<Ref>>(), 24);
    }

    #[test]
    fn the_persistent_space_dedups_and_keeps_ranges() {
        let s = Spaces::new();
        let v = s.build(Var(3));
        assert_eq!(s.build(Var(3)), v);
        assert!(!v.in_region());
        let f = s.build(Free(2));
        let a = s.build(App(v, f));
        assert_eq!((s.loose_at(a), s.free_at(a)), (4, 3));
        let l = s.build(Lam(f, s.build(Var(0))));
        assert_eq!((s.loose_at(l), s.free_at(l)), (0, 3));
        let z = s.build(Sort(0));
        assert_eq!(s.loose_at(s.build(Pair(v, z, z))), 3, "a pair's family sits under a binder");
    }

    /// `height_at` is the tree's height (a leaf 0), in both spaces and through `persist`.
    #[test]
    fn nodes_keep_their_height() {
        fn walk(s: &Spaces, r: Ref) -> u8 {
            let mut h = 0;
            s.node_at(r).for_kids(|c, _| h = h.max(walk(s, *c) + 1));
            h
        }
        let s = Spaces::new();
        let v = s.build(Var(0));
        let a = s.build(App(v, v));
        let l = s.build(Lam(a, s.build(Pair(a, v, s.build(Sort(0))))));
        assert!(s.open());
        let t = s.build(App(l, s.build(Var(5))));
        for r in [v, a, l, t, s.persist(t)] {
            assert_eq!(s.height_at(r), walk(&s, r));
        }
        assert_eq!(s.height_at(t), 4);
        s.close();
    }

    #[test]
    fn a_region_dedups_and_prefers_old_persistent_nodes() {
        let s = Spaces::new();
        let old = s.build(Var(1));
        assert!(s.open());
        assert!(!s.open(), "a nested open joins the region");
        assert_eq!(s.build(Var(1)), old, "a persistent hit below w");
        let v = s.build(Var(7));
        assert!(v.in_region());
        assert_eq!(s.build(Var(7)), v);
        let a = s.build(App(v, old));
        assert!(a.in_region());
        assert_eq!(s.build(App(v, old)), a);
        s.close();
    }

    #[test]
    fn persist_copies_once_and_records_twins() {
        let s = Spaces::new();
        assert!(s.open());
        let g = s.epoch();
        let v = s.build(Var(9));
        let t = s.build(App(v, v));
        let before = s.persistent_len();
        let p = s.persist(t);
        assert_eq!(s.persist(t), p, "memoised");
        assert_eq!(s.persistent_len(), before + 2, "Var(9) and the App, once each");
        assert!(!p.in_region());
        assert_eq!(s.resolve(p, g), t, "a copy reads as its twin while the region is open");
        // Invariant I: the same structure built again is the region node, not the copy at or above w.
        assert_eq!(s.build(Var(9)), v);
        assert_eq!(s.build(App(v, v)), t);
        s.close();
        assert_eq!(s.resolve(p, 0), p);
        let App(c, d) = s.node_at(p) else { panic!("persist changed the constructor") };
        assert!(c == d && !c.in_region() && s.node_at(c) == Var(9));
        assert!(s.open());
        assert_eq!(s.build(Var(9)), c, "the next region finds the copy below its w");
        s.close();
    }

    #[test]
    #[should_panic(expected = "dead handle")]
    fn a_ref_from_a_closed_region_is_dead() {
        let s = Spaces::new();
        assert!(s.open());
        let (r, g) = (s.build(Var(5)), s.epoch());
        s.close();
        assert!(!s.live(r, g));
        assert!(s.open());
        let fresh = s.build(Var(6));
        assert_eq!(fresh.0, r.0, "the new region reuses the index, so only the generation tells them apart");
        s.resolve(r, g);
    }

    #[test]
    fn parents_count_builds_not_hits() {
        let s = Spaces::new();
        assert!(s.open());
        let x = s.build(Var(3));
        let a = s.build(App(x, x));
        assert_eq!((s.parents_at(x), s.parents_at(a)), (2, 0));
        let y = s.build(Var(4));
        let r = s.build(Refl(y));
        assert_eq!(s.build(Refl(y)), r);
        assert_eq!(s.parents_at(y), 1, "a hit adds no parent");
        s.close();
    }
}
