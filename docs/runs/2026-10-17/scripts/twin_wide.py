# twin_wide.py <run root> <arm prefix>...: for every cold loop of the named arms (<prefix>_<salt>/), count the extras that
# are twins of a served law of phases 1-3 of the same family under three normalizations of their two-leaf nodes (lt
# excluded, as in pad_strip.py):
#   leaf  - a node whose width-4 value equals a leaf becomes that leaf, extras only (pad_strip.py's count);
#   leaf2 - the same, applied to the served laws too;
#   class - every node over two leaves becomes its value class's representative (a leaf if one is in the class, else
#           the shortest, then least, two-leaf term), on both sides; the key renames variables before normalizing
#           (`ckey`, as the law generator's does; counts before it renamed after, so they were lower bounds).
# Laws whose sides normalize to the same term are counted apart (trivial). Prints per arm and family: extras, twins per
# normalization, trivial (class).
import sys, os, itertools, collections
here = os.path.dirname(os.path.abspath(__file__))
exec(open(os.path.join(here, "pad_strip.py")).read().split("root = sys.argv[1]")[0])

BIN = [o for o in OPS if o not in ("lt", "shl1")]
TWO = [(o, a, b) for o in BIN for a in LEAVES for b in LEAVES] + [("shl1", a, "0") for a in LEAVES]
def vals(t): return tuple(val(t, e) for e in ASSIGN)
REP = {}
for v, l in ((LEAFVALS[l], l) for l in reversed(LEAVES)): REP[v] = l
for t in sorted(TWO, key=lambda t: (len(show(t)), show(t))):
    REP.setdefault(vals(t), t)
ccache = {}
def norm_class(t):
    if isinstance(t, str): return t
    a, b = norm_class(t[1]), norm_class(t[2])
    n = (t[0], a, b)
    if isinstance(a, str) and isinstance(b, str) and t[0] != "lt":
        if n not in ccache: ccache[n] = REP[vals(n)]
        return ccache[n]
    return n

def nkey(a, b, f):
    sa, sb = show(f(parse(a))), show(f(parse(b)))
    return None if sa == sb else key(sa, sb)

PERMS = list(itertools.permutations("xyz"))
def rename(t, p):
    if isinstance(t, str): return p["xyz".index(t)] if t in ("x", "y", "z") else t
    return (t[0], rename(t[1], p), rename(t[2], p))

# the law generator's key (spec §1): rename first, then normalize, least text over the six renamings and both side
# orders; None if the sides normalize to one term (unrenamed)
def ckey(a, b):
    ta, tb = parse(a), parse(b)
    if show(norm_class(ta)) == show(norm_class(tb)): return None
    return min(f"{show(norm_class(rename(l, p)))} = {show(norm_class(rename(r, p)))}" for p in PERMS for l, r in ((ta, tb), (tb, ta)))

root, prefixes = sys.argv[1], sys.argv[2:]
for pre in prefixes:
    tot = collections.Counter()
    for arm in sorted(os.listdir(root)):
        if not (arm.startswith(pre + "_") and arm[len(pre) + 1:].isdigit()): continue
        d = os.path.join(root, arm)
        for fam in ["cmp3d", "add3", "sbo3"]:
            loops = [os.path.join(d, f"cold_{fam}_{p}_none") for p in (1, 2, 3)]
            if not all(os.path.isdir(l) for l in loops): continue
            served = [l for lp in loops for f in ("laws_serve_0.txt", "laws_serve_100.txt", "laws_serve_200.txt")
                      for l in laws(os.path.join(lp, f))]
            raw = {key(a, b) for a, b in served}
            s_leaf = {nkey(a, b, strip) for a, b in served}
            s_class = {ckey(a, b) for a, b in served}
            for lp in loops:
                for a, b in laws(os.path.join(lp, "laws_extra_0.txt")):
                    tot[(fam, "extras")] += 1
                    kl, kc = nkey(a, b, strip), ckey(a, b)
                    tot[(fam, "leaf")] += kl is not None and kl in raw
                    tot[(fam, "leaf2")] += kl is not None and kl in s_leaf
                    tot[(fam, "class")] += kc is not None and kc in s_class
                    tot[(fam, "trivial")] += kc is None
    for fam in ["cmp3d", "add3", "sbo3"]:
        print(pre, fam, *(f"{c} {tot[(fam, c)]}" for c in ("extras", "leaf", "leaf2", "class", "trivial")))
