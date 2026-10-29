import re
import sys

# usage: an9.py <run id>: node visits against distinct normalize arguments and distinct lookup asks, per level (O mode)
run = sys.argv[1]
base = r"C:\Users\Winston Li\AppData\Local\claude-runs\tatic" + "\\" + run + r"\out.log"
agg = {}
for line in open(base, encoding="utf-8", errors="replace"):
    m = re.match(r"NP pass=(\d+) salt=(\d+) L=(\d+) i=(\d+) ops=(\S+) laws=(\d+) same=(\w+) secs=([\d.]+) pf=(\d+) private_mb=(\d+) ws_mb=(\d+) ?(.*)", line.strip())
    if not m:
        continue
    d = {}
    for kv in m[12].split():
        k, v = kv.split("=")
        d[k] = int(v)
    a = agg.setdefault(int(m[3]), dict(nodes=0, orig=0, asks=0, n=0))
    a["n"] += 1
    a["nodes"] += d.get("NODE", 0)
    a["orig"] += d.get("O_ORIG", 0)
    a["asks"] += sum(d.get(o, 0) for o in ("O_OWN", "O_SAMESTREAM", "O_OTHERSTREAM_SAMELEVEL", "O_OTHERSTREAM_OTHERLEVEL", "O_OTHERSALT"))
for L, a in sorted(agg.items()):
    print(f"L={L}: {a['n']} builds, node visits {a['nodes']}, distinct normalize arguments {a['orig']} ({a['nodes']/a['orig']:.1f} visits each), distinct lookup keys {a['asks']} ({a['nodes']/a['asks']:.1f} visits each)")
