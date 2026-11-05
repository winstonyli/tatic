// --- stack growth ----------------------------------------------------------
//
// Every traversal in this module recurses over `Expr` structure, and
// `whnf`/`nf` also recurse once per reduction step, so native stack use
// grows with both a term's depth and its reduction length. Measured
// before this existed: a debug build on a 1 MB thread (the Windows main
// thread) overflowed at depth ~90, a release build at ~450-570
// (`RELATED_WORK.md` 31). Rather than hand-convert `infer`/`check` into
// an explicit continuation machine -- hundreds of new lines inside the
// trusted kernel, no longer reading like the typing rules they implement
// -- each recursive entry point runs through `grow`, which spills onto a
// fresh heap-allocated stack segment when the current one runs low. The
// approach and constants are rustc's own `ensure_sufficient_stack`; the
// per-call check is this module's own, because stacker's measured too
// slow to make at every node (see `FLOOR`).

/// Headroom below which `grow` switches to a new segment: enough for the
/// deepest chain of un-wrapped frames between two wrapped calls.
const RED_ZONE: usize = 100 * 1024;
/// Size of each new segment `grow` allocates.
const STACK_PER_RECURSION: usize = 1024 * 1024;
/// Size of the one segment a large `check_in` runs on. On Windows stacker builds a fiber per
/// segment and frees it on return, so a deep recursion that straddles a segment boundary pays that
/// cost at every crossing (65k+ times at n=512, a third of the CPU in page faults, doc section 76).
/// Starting the check on a segment big enough that it never reaches the end avoids it, and a deeper
/// recursion still chains further segments. Its pages cost no RAM until touched, but stacker's
/// `CreateFiber` commits all of it: about 150 MB of a sweep worker's peak commit (PARKED.md, "Large
/// `check_in` segments that commit only what they touch").
pub(super) const CHECK_SEGMENT: usize = 64 * 1024 * 1024;

thread_local! {
    /// The lowest stack address the current segment can reach with
    /// [`RED_ZONE`] still to spare; `usize::MAX` -- "unknown", which
    /// every check fails -- until [`grow_slow`] first learns it on this
    /// thread. Tracked here rather than asking stacker each
    /// time: `stacker::remaining_stack` measured 8.9 ns a call on Windows
    /// (a lazily-initialized thread-local plus a non-inlined assembly
    /// call), and at one check per `shift`/`==`/`Drop` node that nearly
    /// doubled every proof benchmark. This check is a local's address
    /// against a const thread-local, ~1 ns.
    static FLOOR: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) };
}

/// An address inside the current frame -- close enough to the stack
/// pointer, with [`RED_ZONE`] of slack.
#[inline(always)]
fn stack_addr() -> usize {
    let here = 0u8;
    std::hint::black_box(&here) as *const u8 as usize
}

/// Whether at least [`RED_ZONE`] bytes of the current segment remain.
#[inline(always)]
fn stack_ok() -> bool {
    stack_addr() > FLOOR.with(|f| f.get())
}

/// Runs `f`, first moving onto a fresh stack segment if fewer than
/// [`RED_ZONE`] bytes remain. Wraps the body of every recursive function
/// in this module, and `Debug` for `Expr` -- so their depth is bounded by
/// heap, not native stack.
#[inline(always)]
pub fn grow<R>(f: impl FnOnce() -> R) -> R {
    if stack_ok() { f() } else { grow_slow(f) }
}

/// [`grow`]'s slow path: the first check on a thread (`FLOOR` unknown),
/// or a segment genuinely running low. Keeps `FLOOR` describing whichever
/// segment is current: set on entry to a new one, restored on the way
/// out -- by a guard, so an unwinding panic restores it too.
///
/// Outside any segment of ours, `FLOOR` unknown means this is the thread's
/// own stack, learned once and kept. Where stacker cannot measure that
/// stack, `FLOOR` stays unknown and every call grows a fresh segment:
/// slow, but never unprotected.
#[cold]
#[inline(never)]
fn grow_slow<R>(f: impl FnOnce() -> R) -> R {
    fn floor_here() -> Option<usize> {
        stacker::remaining_stack().map(|left| stack_addr().saturating_sub(left) + RED_ZONE)
    }
    if FLOOR.with(|f| f.get()) == usize::MAX
        && let Some(floor) = floor_here()
    {
        FLOOR.with(|f| f.set(floor));
        if stack_ok() {
            return f();
        }
    }
    on_segment(STACK_PER_RECURSION, f)
}

thread_local! {
    static SEGMENT_SWITCHES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many times this thread has moved onto a new stack segment (by `grow` or a large `check_in`).
/// A segment is a fiber on Windows, so a recursion that crosses a boundary over and over is costly
/// (doc section 76): tests read this to catch a return of that.
pub fn segment_switches() -> u64 {
    SEGMENT_SWITCHES.with(|c| c.get())
}

/// Runs `f` on a new stack segment of `size` bytes, with `FLOOR` describing it meanwhile.
pub(super) fn on_segment<R>(size: usize, f: impl FnOnce() -> R) -> R {
    SEGMENT_SWITCHES.with(|c| c.set(c.get() + 1));
    fn floor_here() -> Option<usize> {
        stacker::remaining_stack().map(|left| stack_addr().saturating_sub(left) + RED_ZONE)
    }
    struct Restore(usize);
    impl Drop for Restore {
        fn drop(&mut self) {
            FLOOR.with(|f| f.set(self.0));
        }
    }
    stacker::grow(size, || {
        let _restore = Restore(FLOOR.with(|f| f.replace(floor_here().unwrap_or(usize::MAX))));
        f()
    })
}

