"""Keep the candidate rules (lines `lhs -> rhs`) that are true at widths 3-6 (every input at width 3 and 4, random at 5-6),
have a left side with an operator, a strictly smaller right side, and right-side variables among the left's.
usage: filter_candidates.py IN... > OUT"""
import itertools, random, sys
sys.argv, argv = ["x", "/dev/null", "/dev/null"], sys.argv
exec(open("scripts/corpus_augment.py").read().split("corpus = [x.strip()")[0])

def leaves_ok(t):
    return t in ("x", "y", "z", "0", "-1") if isinstance(t, str) else t[0] in COMM | {"sub"} and leaves_ok(t[1]) and leaves_ok(t[2])

def size(t):
    return 1 if isinstance(t, str) else 1 + size(t[1]) + size(t[2])

def vars_of(t):
    return {t} & set("xyz") if isinstance(t, str) else vars_of(t[1]) | vars_of(t[2])

def ev(t, e, m):
    if isinstance(t, str):
        return 0 if t == "0" else m if t == "-1" else e[t]
    a, b = ev(t[1], e, m), ev(t[2], e, m)
    return {"add": (a + b) & m, "and": a & b, "or": a | b, "xor": a ^ b, "sub": (a - b) & m}[t[0]]

random.seed(1)
seen, kept = set(), 0
for path in argv[1:]:
    for line in open(path):
        line = line.strip()
        if " -> " not in line or line in seen:
            continue
        seen.add(line)
        try:
            l, r = (parse(x) for x in line.split(" -> "))
        except Exception:
            continue
        if not (leaves_ok(l) and leaves_ok(r)) or isinstance(l, str) or size(r) >= size(l) or not vars_of(r) <= vars_of(l) or show(l) != line.split(" -> ")[0]:
            continue
        ok = True
        for w in (3, 4, 5, 6):
            m = (1 << w) - 1
            pts = itertools.product(range(m + 1), repeat=3) if w <= 4 else ((random.randint(0, m),) * 0 + tuple(random.randint(0, m) for _ in range(3)) for _ in range(3000))
            if any(ev(l, dict(zip("xyz", p)), m) != ev(r, dict(zip("xyz", p)), m) for p in pts):
                ok = False
                break
        if ok:
            kept += 1
            print(line)
print(f"{len(seen)} candidates, {kept} true and smaller", file=sys.stderr)
