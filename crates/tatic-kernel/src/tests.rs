use super::*;

/// [`super::instantiate`] and the other internals below take the thread's `Spaces`; the tests call them without it.
fn instantiate(e: &Expr, a: &Expr, d: u32) -> Expr {
    with_spaces(|s| super::instantiate(s, e, a, d))
}
fn instantiate_n(e: &Expr, args: &[&Expr], d: u32) -> Expr {
    with_spaces(|s| super::instantiate_n(s, e, args, d))
}
fn subst_top(body: &Expr, a: &Expr) -> Expr {
    with_spaces(|s| super::subst_top(s, body, a))
}
fn is_var_free(e: &Expr, idx: u32) -> bool {
    with_spaces(|s| super::is_var_free(s, e, idx))
}
fn nf(e: &Expr) -> Expr {
    normalize(e)
}
fn hc_uses(x: &Expr, d: u32, m: u32) -> bool {
    with_spaces(|s| hc::uses(s, x, d, m))
}
fn hc_low(x: &Expr) -> bool {
    with_spaces(|s| hc::low(s, x))
}
fn hc_lowest_loose(x: &Expr, d: u32, memo: &mut IdMap<(Key, u32), u32>) -> u32 {
    with_spaces(|s| hc::lowest_loose(s, x, d, memo))
}

/// Asserts `run(large)` costs under `max_ratio` times `run(small)` (plus `noise`), for one of
/// three small-then-large pairs. `run(n)` builds its size-`n` terms and returns the cost of the
/// work alone: `worked`, the change in `work()`, which is the same on every run and every machine
/// (`noise` 0), or `timed`, nanoseconds, for code the counter doesn't see (`TIMER_NOISE`). The
/// runs go on a thread of their own, each given 20 s, so a regression to quadratic or exponential
/// cost fails within seconds instead of hanging the suite. With `noise` dominating, the check reads
/// "the large size stays cheap": pick it so a walk of the tree would take seconds.
fn assert_scales(what: &str, small: u32, large: u32, max_ratio: u32, noise: u64, run: impl Fn(u32) -> u64 + Send + 'static) {
    use std::sync::{Arc, atomic::{AtomicBool, Ordering}, mpsc};
    use std::time::Duration;
    struct Stop(Arc<AtomicBool>);
    impl Drop for Stop {
        fn drop(&mut self) {
            self.0.store(true, Ordering::Relaxed);
        }
    }
    let stop = Stop(Arc::new(AtomicBool::new(false)));
    let (tx, rx) = mpsc::channel();
    let flag = stop.0.clone();
    std::thread::spawn(move || {
        for n in [small, large].repeat(3) {
            if flag.load(Ordering::Relaxed) || tx.send(run(n)).is_err() {
                return;
            }
        }
    });
    let next = |n: u32, wait: Duration, done: &[(u64, u64)]| match rx.recv_timeout(wait) {
        Ok(t) => t,
        Err(mpsc::RecvTimeoutError::Timeout) => panic!("{what}: n = {n} still running after {wait:?}, done {done:?}"),
        Err(mpsc::RecvTimeoutError::Disconnected) => panic!("{what}: a run panicked"),
    };
    let mut pairs = vec![];
    for _ in 0..3 {
        let short = next(small, Duration::from_secs(20), &pairs);
        let budget = short * max_ratio as u64 + noise;
        let long = next(large, Duration::from_secs(20), &pairs);
        if long <= budget {
            return;
        }
        pairs.push((short, long));
    }
    panic!("{what}: (n = {small}, n = {large}) took {pairs:?}, over {max_ratio}x each");
}
/// Nanoseconds of timer noise for a timed `assert_scales`.
const TIMER_NOISE: u64 = 5_000_000;

/// `run(n)` cost for `assert_scales`: the kernel work `f` does on this thread.
fn worked(f: impl FnOnce()) -> u64 {
    let w = work();
    f();
    work() - w
}

/// `run(n)` cost for `assert_scales`: the nanoseconds `f` takes.
fn timed(f: impl FnOnce()) -> u64 {
    let t = std::time::Instant::now();
    f();
    t.elapsed().as_nanos() as u64
}
fn hc_whnf_get(x: &Expr) -> Option<Expr> {
    with_spaces(|s| hc::whnf_get(s, x))
}

/// Replace `Var(j)` with `s` throughout `e`: the reference `subst_top`
/// is checked against, as `shift(&subst(body, 0, &shift(s, 0, 1)), 0, -1)`.
fn subst(e: &Expr, j: u32, s: &Expr) -> Expr {
    grow(|| match e.node() {
        Node::Var(k) => {
            if k == j {
                *s
            } else {
                var(k)
            }
        }
        n @ (Node::Sort(_) | Node::Const(_) | Node::Free(_)) => mk(n),
        n => mk(n.map_kids(|c, under| if under { subst(&c, j + 1, &shift(s, 0, 1)) } else { subst(&c, j, s) })),
    })
}

/// A splitmix64 stream, for the randomised tests below.
fn splitmix(seed: u64) -> impl FnMut() -> usize {
    let mut rng = tatic_rng::SplitMix64::new(seed);
    move || rng.next_u64() as usize
}

/// A random term with every `Expr` shape, built from a pool of nodes so
/// children are shared. Its leaves are `Var(0..4)`, `Sort(0)`,
/// `Const(0)`, `Const(1)`, `Free(0)` and `Free(2)`, so it has both open
/// and closed subterms at every binder depth, and terms with and
/// without a `Free`.
fn random_term(next: &mut impl FnMut() -> usize) -> Expr {
    let mut pool: Vec<Expr> = (0..4)
        .map(var)
        .chain([sort(0), mk(Node::Const(0)), mk(Node::Const(1)), mk(Node::Free(0)), mk(Node::Free(2))])
        .collect();
    for _ in 0..12 {
        let kind = next() % 14;
        let mut c = || pool[next() % pool.len()];
        let node = match kind {
            0 => Node::Pi(c(), c()),
            1 => Node::Lam(c(), c()),
            2 | 3 => Node::App(c(), c()),
            4 => Node::Id(c(), c(), c()),
            5 => Node::Refl(c()),
            6 => Node::J { motive: c(), base: c(), a: c(), b: c(), p: c() },
            7 => Node::W(c(), c()),
            8 => Node::Sup(c(), c()),
            9 => Node::WRec { motive: c(), children_ty: c(), step: c(), target: c() },
            10 => Node::Sigma(c(), c()),
            11 => Node::Pair(c(), c(), c()),
            12 => Node::SigRec { motive: c(), step: c(), target: c() },
            _ => Node::Sort(1),
        };
        pool.push(mk(node));
    }
    *pool.last().unwrap()
}

/// The pre-§64 `is_var_free`, kept as the reference for the new one and for
/// `loose`. It walks the whole term and reads no cached range.
fn is_var_free_ref(e: &Expr, idx: u32) -> bool {
    grow(|| match e.node() {
        Node::Var(k) => k == idx,
        Node::Sort(_) | Node::Const(_) | Node::Free(_) => false,
        n => {
            let mut any = false;
            n.for_kids(|c, under| any = any || is_var_free_ref(c, idx + under as u32));
            any
        }
    })
}

/// The pre-§64 `shift`, kept as the reference for the new one. It rebuilds
/// every node, so it's also a deep copy that shares nothing.
fn shift_ref(e: &Expr, cutoff: u32, amount: i32) -> Expr {
    grow(|| match e.node() {
        Node::Var(k) => {
            if k >= cutoff {
                var((k as i32 + amount) as u32)
            } else {
                var(k)
            }
        }
        n @ (Node::Sort(_) | Node::Const(_) | Node::Free(_)) => mk(n),
        n => mk(n.map_kids(|c, under| shift_ref(&c, cutoff + under as u32, amount))),
    })
}

/// The pre-§64 `instantiate`, kept as the reference for the new one.
fn instantiate_ref(e: &Expr, s: &Expr, d: u32) -> Expr {
    grow(|| match e.node() {
        Node::Var(k) => {
            if k == d {
                shift_ref(s, 0, d as i32)
            } else if k > d {
                var(k - 1)
            } else {
                var(k)
            }
        }
        n @ (Node::Sort(_) | Node::Const(_) | Node::Free(_)) => mk(n),
        n => mk(n.map_kids(|c, under| instantiate_ref(&c, s, d + under as u32))),
    })
}

/// The largest `Free` level a walk of the whole term finds, plus one
/// (0 with none): the reference for the cached `free` range.
fn free_ref(e: &Expr) -> u32 {
    grow(|| match e.node() {
        Node::Free(l) => l + 1,
        n => {
            let mut m = 0;
            n.for_kids(|c, _| m = m.max(free_ref(c)));
            m
        }
    })
}

/// A random `Expr` of every variant, ill-typed as often as not, with
/// indices small enough that `Var(0)` is often free and often not.
fn random_expr(seed: &mut tatic_rng::SplitMix64, fuel: u32) -> Expr {
    let mut next = || seed.next_u64();
    let pick = next();
    let k = (next() % 4) as u32;
    if fuel == 0 || pick % 4 == 0 {
        return if pick % 8 == 0 { sort(k % 2) } else { var(k) };
    }
    let mut sub = || random_expr(seed, fuel - 1);
    match (pick >> 3) % 13 {
        0 => pi(sub(), sub()),
        1 => lam(sub(), sub()),
        2 => app(sub(), sub()),
        3 => id(sub(), sub(), sub()),
        4 => refl(sub()),
        5 => jelim(sub(), sub(), sub(), sub(), sub()),
        6 => wty(sub(), sub()),
        7 => sup(sub(), sub()),
        8 => wrec(sub(), sub(), sub(), sub()),
        9 => sigma(sub(), sub()),
        10 => pair(sub(), sub(), sub()),
        11 => sigrec(sub(), sub(), sub()),
        _ => app(sub(), sub()),
    }
}

/// `d (d (... (d x)))`, `n` deep, with `d = \x. x x`: a normal form of 2^n nodes.
fn doubling(n: u32) -> Expr {
    (0..n).fold(var(0), |t, _| app(lam(sort(0), app(var(0), var(0))), t))
}

/// Wraps some of `e`'s subterms in a redex that reduces back to them,
/// `(\_. x) Sort(0)` with `x` shifted under the new binder.
fn with_redexes(e: &Expr, seed: &mut tatic_rng::SplitMix64) -> Expr {
    let wrap = seed.next_u64().is_multiple_of(4);
    let rebuilt = match e.node() {
        n @ (Node::Pi(..) | Node::Lam(..) | Node::App(..) | Node::Id(..) | Node::Sigma(..) | Node::Pair(..)) => {
            mk(n.map_kids(|c, _| with_redexes(&c, seed)))
        }
        _ => *e,
    };
    if wrap { app(lam(sort(0), shift(&rebuilt, 0, 1)), sort(0)) } else { rebuilt }
}

/// The argument of each application in `e`'s spine, outermost
/// first.
fn spine_args(e: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    let mut e = *e;
    while let Node::App(f, a) = e.node() {
        out.push(a);
        e = f;
    }
    out
}

/// `A : Type0` and `a : A` as globals: the environment the tests below
/// type constants in.
fn two_globals() -> Globals {
    let mut g = Globals::new();
    g.push_back(persist(sort(0)));
    g.push_back(persist(mk(Node::Const(0))));
    g
}


mod substitution;
mod conversion;
mod memo;
mod worked;
mod typing;
mod rules;
mod scopes;
