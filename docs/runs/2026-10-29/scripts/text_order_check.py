# text_order_check.py: checks that `Term::show`'s text order (tests/church_bv/rewrite.rs, `show_into`: `op(a, b)` with
# OP_INFO's names and VARS) equals the lexicographic order of a term's preorder tokens ranked as text, on every term to
# size 5 (node count) and on random terms to size 17, and that 5*size-3 bounds the text's length. The basis of S1 in
# docs/tier-cycle.md, "Survey: the open-law filter, `Term::show` and mimalloc's purge". Pure Python, no inputs; run as
# `python -P text_order_check.py < /dev/null`.
import random

OPS = ["add", "and", "or", "xor", "sub", "lt", "shl1", "shr1"]
VARS = ["x", "y", "z", "u", "v", "w", "p", "q"]
LEAVES = VARS + ["0", "-1"]
TOK = sorted(LEAVES + [o + "(" for o in OPS])
RANK = {t: i for i, t in enumerate(TOK)}
print("token order:", TOK)


def show(t):
    if isinstance(t, str):
        return t
    o, a, b = t
    return f"{o}({show(a)}, {show(b)})"


def key(t):
    out = []

    def walk(t):
        if isinstance(t, str):
            out.append(RANK[t])
            return
        o, a, b = t
        out.append(RANK[o + "("])
        walk(a)
        walk(b)

    walk(t)
    return tuple(out)


by_size = {1: list(LEAVES)}
for s in (3, 5):
    by_size[s] = [(o, a, b) for sa in range(1, s - 1, 2) for o in OPS for a in by_size[sa] for b in by_size[s - 1 - sa]]
allt = [t for s in sorted(by_size) for t in by_size[s]]
assert sorted(allt, key=show) == sorted(allt, key=key), "order differs (exhaustive)"
print(f"every term to size 5 ({len(allt)}): text order == token-rank order")

random.seed(1)


def rnd(n):
    if n <= 1:
        return random.choice(LEAVES)
    k = random.randrange(1, n, 2)
    return (random.choice(OPS), rnd(k), rnd(n - 1 - k))


R = list({show(t): t for t in (rnd(random.choice(range(1, 18, 2))) for _ in range(60000))}.values())
assert sorted(R, key=show) == sorted(R, key=key), "order differs (random)"
print(f"{len(R)} distinct random terms to size 17: text order == token-rank order")

size = lambda t: 1 if isinstance(t, str) else 1 + size(t[1]) + size(t[2])
slack = [5 * size(t) - 3 - len(show(t)) for t in allt + R]
assert min(slack) == 0, "5*size-3 is not a tight upper bound"
print("5*size-3 bounds the text's length and is reached")
