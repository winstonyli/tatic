import re
import sys

# usage: an7.py <run id>: provenance of the distinct terms each build asks (O mode), per salt and level
run = sys.argv[1]
base = r"C:\Users\Winston Li\AppData\Local\claude-runs\tatic" + "\\" + run + r"\out.log"
O = ["O_OWN", "O_SAMESTREAM", "O_OTHERSTREAM_SAMELEVEL", "O_OTHERSTREAM_OTHERLEVEL", "O_OTHERSALT"]
agg = {}
for line in open(base, encoding="utf-8", errors="replace"):
    m = re.match(r"NP pass=(\d+) salt=(\d+) L=(\d+) i=(\d+) ops=(\S+) laws=(\d+) same=(\w+) secs=([\d.]+) pf=(\d+) private_mb=(\d+) ws_mb=(\d+) ?(.*)", line.strip())
    if not m:
        continue
    d = {}
    for kv in m[12].split():
        k, v = kv.split("=")
        d[k] = int(v)
    key = (int(m[2]), int(m[3]))
    a = agg.setdefault(key, dict(n=0, nodes=0, miss=0, **{o: 0 for o in O}))
    a["n"] += 1
    a["nodes"] += d.get("NODE", 0)
    a["miss"] += d.get("LK_MISS", 0)
    for o in O:
        a[o] += d.get(o, 0)
for (salt, L), a in sorted(agg.items()):
    tot = sum(a[o] for o in O)
    print(f"salt {salt} L={L}: {a['n']} streams, {tot} distinct terms asked in total (summed over streams), LK_MISS {a['miss']}")
    for o in O:
        print(f"    {o:28s} {a[o]:9d}  {100*a[o]/tot:5.1f}%")
