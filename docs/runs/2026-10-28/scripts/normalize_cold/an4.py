import re
import sys

# usage: an4.py <run id> [L]: hit-part ns/node (normalize time minus miss time, per node) against page faults per build
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
    d = dict(pass_=int(m[1]), L=int(m[3]), i=int(m[4]), pf=int(m[9]), priv=int(m[10]))
    for kv in m[12].split():
        k, v = kv.split("=")
        d[k] = int(v)
    rows.append(d)
# split builds into pf-free (< 1000 faults) and pf-heavy (>= 10000) and compare the hit-part cost per node and per miss-free build
for name, sel in (("pf < 1000", lambda r: r["pf"] < 1000), ("pf >= 10000", lambda r: r["pf"] >= 10000)):
    for passname, pp in (("cold (pass 1)", lambda r: r["pass_"] == 1), ("warm (pass 2 or 0)", lambda r: r["pass_"] != 1)):
        s = [r for r in rows if r["L"] == L and sel(r) and pp(r) and r.get("NODE", 0) > 50000]
        if not s:
            continue
        n = sum(r["NODE"] for r in s)
        miss = sum(r.get("LK_MISS_T", 0) + r.get("V_EVAL_T", 0) + r.get("V_INS_T", 0) for r in s) / hz
        norm = sum(r["NORM_T"] for r in s) / hz
        pf = sum(r["pf"] for r in s)
        print(f"L={L} {name:12s} {passname:19s}: {len(s):3d} builds, {n/1e6:6.2f} M nodes, normalize {norm:6.2f} s, misses {miss:5.2f} s, hit part {1e9*(norm-miss)/n:5.0f} ns/node, faults {pf}")
