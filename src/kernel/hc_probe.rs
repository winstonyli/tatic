//! Probes for hash-consing and a global `instantiate` memo (bit-vector design doc section 58):
//! a simulated intern table gives each node the id its structure would have, from its constructor,
//! leaf value and children's ids. Nothing here changes any result.

use super::*;
use std::cell::{Cell, RefCell};
use std::hash::{Hash, Hasher};

/// Repeat statistics per kind of operation: 0 `instantiate_n`, 1 `shift`, 2 `whnf_step`, 3
/// `conv_whnf`.
pub const KINDS: usize = 4;

thread_local! {
    static TABLE: RefCell<HashMap<u64, u64>> = RefCell::new(HashMap::new());
    /// 0 nodes built, 1 of them new to the table.
    static BUILT: [Cell<u64>; 2] = const { [const { Cell::new(0) }; 2] };
    static SEEN: RefCell<[HashSet<u64>; KINDS]> = RefCell::new(Default::default());
    /// Per kind: 0 calls, 1 maximal repeated calls, 2 work inside them, 3 work in all depth-0
    /// calls, 4 depth-0 calls, 5 depth-0 repeats, 6 work inside depth-0 repeats.
    static STATS: [[Cell<u64>; 8]; KINDS] = const { [const { [const { Cell::new(0) }; 8] }; KINDS] };
    static DEPTH: [Cell<u32>; KINDS] = const { [const { Cell::new(0) }; KINDS] };
    static IN_REPEAT: [Cell<bool>; KINDS] = const { [const { Cell::new(false) }; KINDS] };
}

/// Work done so far, for the kind: its own walk's visits for `instantiate_n` and `shift`, the
/// sum of all three walks for the others.
fn work(kind: usize) -> u64 {
    WALKS.with(|w| match kind {
        0 => w[0].get(),
        1 => w[1].get(),
        _ => w[0].get() + w[1].get() + w[2].get(),
    })
}

fn structure_hash(e: &Expr) -> u64 {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    std::mem::discriminant(e).hash(&mut h);
    match e {
        Expr::Var(k) | Expr::Sort(k) | Expr::Const(k) | Expr::Free(k) => k.hash(&mut h),
        _ => {
            same_shape(e, e, |p, _| {
                p.canon().hash(&mut h);
                true
            });
        }
    }
    h.finish()
}

fn id_of(e: &Expr, count: bool) -> u64 {
    let h = structure_hash(e);
    TABLE.with(|t| {
        let mut t = t.borrow_mut();
        let next = t.len() as u64;
        let new = !t.contains_key(&h);
        let id = *t.entry(h).or_insert(next);
        if count {
            BUILT.with(|b| {
                b[0].set(b[0].get() + 1);
                if new {
                    b[1].set(b[1].get() + 1);
                }
            });
        }
        id
    })
}

pub fn intern(e: &Expr) -> u64 {
    id_of(e, true)
}

/// (nodes built, distinct structures among them new to the table) since the last call.
pub fn take_built() -> (u64, u64) {
    BUILT.with(|b| (b[0].replace(0), b[1].replace(0)))
}

pub fn take_inst() -> [[u64; 8]; KINDS] {
    STATS.with(|c| std::array::from_fn(|k| std::array::from_fn(|i| c[k][i].replace(0))))
}

/// Guard for one call of kind `kind`: notes whether the same key was seen before, and the work a
/// memo hit would have skipped.
pub struct Guard {
    kind: usize,
    v0: u64,
    repeat: bool,
    outer_repeat: bool,
    top: bool,
}

fn start(kind: usize, key: u64) -> Guard {
    let repeat = !SEEN.with(|s| s.borrow_mut()[kind].insert(key));
    let top = DEPTH.with(|c| c[kind].replace(c[kind].get() + 1)) == 0;
    let outer_repeat = IN_REPEAT.with(|c| c[kind].replace(c[kind].get() || repeat));
    STATS.with(|c| {
        let c = &c[kind];
        c[0].set(c[0].get() + 1);
        if top {
            c[4].set(c[4].get() + 1);
        }
        if repeat && !outer_repeat {
            c[1].set(c[1].get() + 1);
        }
        if top && repeat {
            c[5].set(c[5].get() + 1);
        }
    });
    Guard { kind, v0: work(kind), repeat, outer_repeat, top }
}

impl Drop for Guard {
    fn drop(&mut self) {
        let visits = work(self.kind) - self.v0;
        let k = self.kind;
        DEPTH.with(|c| c[k].set(c[k].get() - 1));
        IN_REPEAT.with(|c| c[k].set(self.outer_repeat));
        STATS.with(|c| {
            let c = &c[k];
            if self.repeat && !self.outer_repeat {
                c[2].set(c[2].get() + visits);
            }
            if self.top {
                c[3].set(c[3].get() + visits);
                if self.repeat {
                    c[6].set(c[6].get() + visits);
                }
            }
        });
    }
}

pub fn inst_enter(e: &Expr, args: &[&Expr], d: u32) -> Guard {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    id_of(e, false).hash(&mut h);
    for a in args {
        id_of(a, false).hash(&mut h);
    }
    d.hash(&mut h);
    start(0, h.finish())
}

pub fn shift_enter(e: &Expr, cutoff: u32, amount: i32) -> Guard {
    let mut h = std::collections::hash_map::DefaultHasher::new();
    id_of(e, false).hash(&mut h);
    (cutoff, amount).hash(&mut h);
    start(1, h.finish())
}

pub fn whnf_enter(e: &Expr) -> Guard {
    start(2, id_of(e, false))
}

pub fn conv_enter(x: &Expr, y: &Expr) -> Guard {
    let (a, b) = (id_of(x, false), id_of(y, false));
    let mut h = std::collections::hash_map::DefaultHasher::new();
    (a.min(b), a.max(b)).hash(&mut h);
    start(3, h.finish())
}
