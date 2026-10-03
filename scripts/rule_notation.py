"""Convert rule lines between the infix syntax (`add(x, y) -> x`) and a prefix one with one token per operator or leaf
(`add x y > x`); every operator is binary, so prefix needs no brackets. usage: rule_notation.py to_prefix|from_prefix [FILE...]
(reads stdin when no file is given)."""
import sys

mode, files = sys.argv[1], sys.argv[2:]
sys.argv = ["x", "/dev/null", "/dev/null"]
exec(open("scripts/corpus_augment.py").read().split("corpus = [x.strip()")[0])

def pre(t):
    return t if isinstance(t, str) else f"{t[0]} {pre(t[1])} {pre(t[2])}"

def unpre(toks):
    t = toks.pop(0)
    if t in ("add", "and", "or", "xor", "sub", "shl1"):
        a = unpre(toks)
        return (t, a, unpre(toks))
    return t

def lines():
    if files:
        for f in files:
            yield from open(f)
    else:
        yield from sys.stdin

for line in lines():
    line = line.strip()
    try:
        if mode == "to_prefix":
            if " -> " in line:
                l, r = line.split(" -> ")
                print(f"{pre(parse(l))} > {pre(parse(r))}")
        else:
            l, r = line.split(" > ")
            tl, tr = l.split(), r.split()
            a, b = unpre(tl), unpre(tr)
            if not tl and not tr:
                print(f"{show(a)} -> {show(b)}")
    except Exception:
        pass
