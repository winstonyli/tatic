# filter_split.py <dir> <exe>: the busy samples of a samply profile of the pin test (pcs.json.gz, frames named as by
# docs/runs/2026-10-18/scripts/prof_named.py, whose loader this runs) inside `stream_laws`' open-law filter (the
# `scoped` closure, `stream_laws::{closure#10}`), split by what the work is: the shuffle, `Classes::normalize` (verdicts
# evaluated and lookups computed on a term's first ask; plans built and dropped, lookup hits and the walk on every
# visit), the width-8 refuter (`r8.agree`) and the closure's own drops. Each sample goes to the first bucket that
# matches, in the order below. Prints shares of all busy samples, then the drops by what is dropped (`Rc`'s drop; the
# frames carry no type). Run as `python -P filter_split.py <dir> <exe> < /dev/null`.
import collections, os, sys

here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, "..", "..", "2026-10-18", "scripts", "prof_named.py")).read()
exec(compile(src[: src.index("tot = len(samples)")], "prof_named.py", "exec"))

TOP = "church_bv::search::stream_laws::{closure#10}"
DROPS = ("core::ptr::drop_glue", "core::ptr::drop_in_place", "alloc::rc::impl$34::drop", "::drop_slow")


def bucket(below):
    has = lambda p: any(p in n for n in below)
    # inside `first_difference`: filling the two vectors (`fill`), else the compare loop
    filling = any(n == "::fill" or n.startswith("::fill ") or "::fill::" in n for n in below)
    comparing = has("::first_difference") and not filling
    if has("church_bv::search::shuffled"):
        return "shuffle"
    if has("::normalize"):
        if has("church_bv::classes::verdict"):
            if has("church_bv::machine::tree_encoding"):
                return "normalize/first ask/verdict: tree search"
            if has("church_bv::rewrite::ValueMemo::exhaustive"):
                return "normalize/first ask/verdict: bitwise, building exhaustive inputs"
            if has("church_bv::rewrite::bitwise_holds"):
                return "normalize/first ask/verdict: bitwise, " + ("comparing" if comparing else "filling")
            return "normalize/first ask/verdict: other"
        if has("church_bv::classes::impl$1::lookup::closure$1"):
            return "normalize/first ask/lookup"
        if has("church_bv::rewrite::Plan::new"):
            return "normalize/every visit/plans built"
        if has("church_bv::classes::Classes::rep") or has("::lookup"):
            return "normalize/every visit/lookup hits"
        if any(n.startswith(DROPS) or n.endswith(DROPS[-1]) for n in below):
            return "normalize/every visit/drops"
        return "normalize/every visit/walk and the rest"
    if has("church_bv::rewrite::ValueMemo::agree"):
        return "refuter: " + ("comparing" if comparing else "filling")
    if any(n.startswith(DROPS) or n.endswith(DROPS[-1]) for n in below):
        return "closure: drops"
    return "closure: rest"


tot, b, drops_in = len(samples), collections.Counter(), collections.Counter()
for ch in samples:
    flat = [n for f in ch for n in (names.get(f[1], [f"exe:{f[1]}"]) if f[0] == "exe" else [f[1]])]
    k = next((i for i, n in enumerate(flat) if n.startswith(TOP)), None)
    if k is None:
        continue
    below = flat[:k]
    w = bucket(below)
    b[w] += 1
    if w.endswith("drops"):
        # what is being dropped: the first frame inside the outermost run of drop glue (`Rc`'s drop, a lock guard's)
        j = max(i for i, n in enumerate(below) if n.startswith(DROPS[:2]))
        while j > 0 and below[j - 1].startswith(DROPS[:2]):
            j -= 1
        drops_in[w.split("/")[0].split(":")[0] + ": " + (below[j - 1] if j else "(leaf)")] += 1
under = sum(b.values())
print(f"busy samples {tot}; under {TOP}: {under} ({100 * under / tot:.2f}%)")
for top in ("shuffle", "normalize/first ask", "normalize/every visit", "normalize", "refuter", "closure"):
    print(f"{100 * sum(v for w, v in b.items() if w.startswith(top)) / tot:6.2f}% {top} (total)")
for w in sorted(b):
    print(f"{100 * b[w] / tot:6.2f}%   {w}")
print("drops, by where and what is dropped:")
for n, v in drops_in.most_common(8):
    print(f"{100 * v / tot:6.2f}%   {n}")
