# pad_strip.py <run_root>: for every cold loop of the pad_* arms, strip each extra law's padding (a node over two leaves
# whose width-4 value equals a leaf becomes that leaf), then classify the stripped law against the family's served laws.
import sys, os, re, itertools, collections

W = 16
VARS = "xyzu"
OPS = {
    "add": lambda a, b: (a + b) % W,
    "sub": lambda a, b: (a - b) % W,
    "xor": lambda a, b: a ^ b,
    "and": lambda a, b: a & b,
    "or": lambda a, b: a | b,
    "shl1": lambda a, b: ((a << 1) | (b & 1)) % W,
    "lt": lambda a, b: int(a < b),
}
TOK = re.compile(r"\s*([a-z0-9]+|-1|\(|\)|,)")

def parse(s):
    toks = TOK.findall(s)
    pos = 0
    def go():
        nonlocal pos
        t = toks[pos]; pos += 1
        if pos < len(toks) and toks[pos] == "(":
            pos += 1; a = go(); assert toks[pos] == ","; pos += 1; b = go(); assert toks[pos] == ")"; pos += 1
            return (t, a, b)
        return t
    r = go(); assert pos == len(toks), s
    return r

def show(t):
    return t if isinstance(t, str) else f"{t[0]}({show(t[1])}, {show(t[2])})"

ASSIGN = list(itertools.product(range(W), repeat=3))
def val(t, env):
    if isinstance(t, str):
        if t == "0": return 0
        if t == "-1": return W - 1
        return env[VARS.index(t)]
    return OPS[t[0]](val(t[1], env), val(t[2], env))
LEAVES = ["x", "y", "z", "0", "-1"]
LEAFVALS = {l: tuple(val(l, e) for e in ASSIGN) for l in LEAVES}
cache = {}
def strip(t):
    if isinstance(t, str): return t
    a, b = strip(t[1]), strip(t[2])
    n = (t[0], a, b)
    if isinstance(a, str) and isinstance(b, str) and t[0] != "lt":
        if n not in cache:
            v = tuple(val(n, e) for e in ASSIGN)
            cache[n] = next((l for l in LEAVES if LEAFVALS[l] == v), None)
        if cache[n] is not None: return cache[n]
    return n

def canon(s):
    seen = []
    def f(m):
        c = m.group(0)
        if c not in seen: seen.append(c)
        return "abcd"[seen.index(c)]
    return re.sub(r"\b[xyzu]\b", f, s)
def key(a, b):
    return min(canon(f"{a} = {b}"), canon(f"{b} = {a}"))
def laws(path):
    out = []
    for l in open(path):
        l = l.strip()
        if " = " in l:
            a, b = l.split(" = ", 1); out.append((a, b))
    return out

root = sys.argv[1]
tot = collections.Counter()
for arm in sorted(os.listdir(root)):
    if not arm.startswith("pad_"): continue
    d = os.path.join(root, arm)
    for fam in ["cmp3d", "add3", "sbo3"]:
        served_any = {}
        loops = [os.path.join(d, f"cold_{fam}_{p}_none") for p in (1, 2, 3)]
        for p, lp in zip((1, 2, 3), loops):
            for bi, f in enumerate(["laws_serve_0.txt", "laws_serve_100.txt", "laws_serve_200.txt"]):
                for a, b in laws(os.path.join(lp, f)):
                    served_any.setdefault(key(a, b), (p, bi))
        for p, lp in zip((1, 2, 3), loops):
            for a, b in laws(os.path.join(lp, "laws_extra_0.txt")):
                sa, sb = show(strip(parse(a))), show(strip(parse(b)))
                if sa == sb: c = "trivial"
                else:
                    hit = served_any.get(key(sa, sb))
                    if hit is None: c = "other"
                    elif hit[0] == p: c = ["own batch 0 (mined)", "own batch 1 (future)", "own batch 2 (future)"][hit[1]]
                    else: c = "another loop's batch"
                tot[(fam, c)] += 1
for fam in ["cmp3d", "add3", "sbo3"]:
    n = sum(v for (f, _), v in tot.items() if f == fam)
    print(fam, n, {c: v for (f, c), v in sorted(tot.items()) if f == fam})
