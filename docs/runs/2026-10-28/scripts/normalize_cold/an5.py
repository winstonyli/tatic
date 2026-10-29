import re
import sys

# usage: an5.py <run id> [L]: faults inside the normalize pairs (PF_NORM) against the build's faults, cost per fault
run = sys.argv[1]
L = int(sys.argv[2]) if len(sys.argv) > 2 else 4
base = r"C:\Users\Winston Li\AppData\Local\claude-runs\tatic" + "\\" + run + r"\out.log"
hz = None
rows = []
for line in open(base, encoding="utf-8", errors="replace"):
    if line.startswith("NP HZ"):
        hz = float(line.split()[2])
    m = re.match(r"NP pass=(\d+) salt=(\d+) L=(\d+) i=(\d+) ops=(\S+) laws=(\d+) same=(\w+) secs=([\d.]+) pf=(\d+) private_mb=(\d+) ws_mb=(\d+) ?(.*)", line.strip())
    if not m:
        continue
    d = dict(pass_=int(m[1]), L=int(m[3]), i=int(m[4]), pf=int(m[9]), priv=int(m[10]), secs=float(m[8]))
    for kv in m[12].split():
        k, v = kv.split("=")
        d[k] = int(v)
    rows.append(d)
s = [r for r in rows if r["L"] == L and r.get("NODE", 0) > 50000]
print("builds", len(s), "pf total", sum(r["pf"] for r in s), "PF_NORM total", sum(r.get("PF_NORM", 0) for r in s))
# least squares: hit-part seconds = a * nodes + b * PF_NORM over all builds (cold and warm, misses subtracted)
import itertools
xs = []
for r in s:
    miss = (r.get("LK_MISS_T", 0) + r.get("V_EVAL_T", 0) + r.get("V_INS_T", 0)) / hz
    hit = r["NORM_T"] / hz - miss
    xs.append((r["NODE"], r.get("PF_NORM", 0), hit))
sxx = sum(n * n for n, p, h in xs); sxp = sum(n * p for n, p, h in xs); spp = sum(p * p for n, p, h in xs)
sxh = sum(n * h for n, p, h in xs); sph = sum(p * h for n, p, h in xs)
det = sxx * spp - sxp * sxp
a = (sxh * spp - sph * sxp) / det
b = (sph * sxx - sxh * sxp) / det
print(f"fit: hit part = {a*1e9:.0f} ns/node + {b*1e6:.2f} us per fault inside normalize")
res = [h - a * n - b * p for n, p, h in xs]
print("rms residual per build %.3f s of mean hit part %.3f s" % ((sum(x * x for x in res) / len(res)) ** 0.5, sum(h for n, p, h in xs) / len(xs)))
# private bytes vs faults: does churn start at a size
for r in sorted(s, key=lambda r: (r["pass_"] != 1, r["i"]))[:0]:
    pass
big = [r for r in s if r["pf"] >= 10000]
small = [r for r in s if r["pf"] < 1000]
print("pf>=10000 builds: private_mb min %d max %d; pf<1000 builds: private_mb min %d max %d" % (min(r["priv"] for r in big), max(r["priv"] for r in big), min(r["priv"] for r in small), max(r["priv"] for r in small)))
print("PF_NORM / pf in the heavy builds: %.3f" % (sum(r.get("PF_NORM", 0) for r in big) / sum(r["pf"] for r in big)))
