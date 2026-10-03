"""Symmetry-augment a rule corpus and split it by rule family (search note section 78).

usage: corpus_augment.py CORPUS HELDOUT_FILE... OUT_PREFIX

A rule's family is the set of rules reachable by renaming x/y/z and swapping the operands of add/and/or/xor
(sound: each is true whenever the rule is). Every family that contains a held-out rule goes to OUT_PREFIX.test;
the other corpus rules, with all their variants, go to OUT_PREFIX.train; every variant of a held-out rule goes to
OUT_PREFIX.heldout. Prints counts."""
import itertools, sys

COMM = {"add", "and", "or", "xor"}

def parse(s):
    s = s.strip()
    if "(" not in s:
        return s
    op, rest = s.split("(", 1)
    rest, depth, cut = rest[:-1], 0, None
    for i, c in enumerate(rest):
        depth += c == "("
        depth -= c == ")"
        if c == "," and depth == 0:
            cut = i
            break
    return (op, parse(rest[:cut]), parse(rest[cut + 1:]))

def show(t):
    return t if isinstance(t, str) else f"{t[0]}({show(t[1])}, {show(t[2])})"

def commutes(t):
    if isinstance(t, str):
        return [t]
    out = []
    for a in commutes(t[1]):
        for b in commutes(t[2]):
            out.append((t[0], a, b))
            if t[0] in COMM:
                out.append((t[0], b, a))
    return out

def rename(t, m):
    return m.get(t, t) if isinstance(t, str) else (t[0], rename(t[1], m), rename(t[2], m))

def variants(rule):
    l, r = (parse(x) for x in rule.split(" -> "))
    out = set()
    for p in itertools.permutations("xyz"):
        m = dict(zip("xyz", p))
        for a in commutes(rename(l, m)):
            for b in commutes(rename(r, m)):
                out.add(f"{show(a)} -> {show(b)}")
    return out

corpus = [x.strip() for x in open(sys.argv[1]) if " -> " in x]
held = [x.strip() for f in sys.argv[2:-1] for x in open(f) if " -> " in x]
held_family = set().union(*(variants(h) for h in held))
train, test = set(), set()
for rule in corpus:
    vs = variants(rule)
    (test if vs & held_family else train).update(vs)
train -= test
for name, data in (("train", train), ("test", test), ("heldout", held_family)):
    open(f"{sys.argv[-1]}.{name}", "w").write("".join(sorted(x + "\n" for x in data)))
print(f"{len(corpus)} corpus rules; held-out rules {len(held)} with {len(held_family)} variants; train {len(train)}, test(corpus-side) {len(test)}")
