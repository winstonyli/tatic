# an2.py <run> [L=4] [stride=4]: per stream, cold normalize time split into miss and hit part, warm normalize time and ns per node, from the NP rows of the run's out.log.
import re
import sys

run = sys.argv[1]
L = int(sys.argv[2]) if len(sys.argv) > 2 else 4
stride = int(sys.argv[3]) if len(sys.argv) > 3 else 4
base = r"C:\Users\Winston Li\AppData\Local\claude-runs\tatic" + "\\" + run + r"\out.log"
rows = {}
hz = None
for line in open(base, encoding="utf-8", errors="replace"):
    if line.startswith("NP HZ"):
        hz = float(line.split()[2])
    m = re.match(r"NP pass=(\d+) salt=(\d+) L=(\d+) i=(\d+) ops=(\S+) laws=(\d+) same=(\w+) secs=([\d.]+) pf=(\d+) private_mb=(\d+) ws_mb=(\d+) ?(.*)", line.strip())
    if not m:
        continue
    d = dict(secs=float(m[8]), pf=int(m[9]), priv=int(m[10]), ops=m[5])
    for kv in m[12].split():
        k, v = kv.split("=")
        d[k] = int(v)
    rows.setdefault("list", []).append((int(m[1]), int(m[2]), int(m[3]), int(m[4]), d))
lst = rows["list"]
print(f"{'stream':14s} {'nodes':>8s} | {'cold norm':>9s} {'miss':>6s} {'hit part':>8s} {'ns/node':>7s} {'pf':>7s} | {'warm norm':>9s} {'ns/node':>7s} {'pf':>7s} | {'cold-warm':>9s} | {'cold secs':>9s} {'warm secs':>9s}")
tot = [0.0] * 8
for p, salt, lv, i, d in lst:
    if p != 1 or lv != L or i % stride:
        continue
    w = [x for x in lst if x[0] == 2 and x[2] == lv and x[3] == i and x[1] == salt][0][4]
    miss = (d.get("LK_MISS_T", 0) + d.get("V_EVAL_T", 0) + d.get("V_INS_T", 0)) / hz
    cold = d["NORM_T"] / hz
    warm = w["NORM_T"] / hz
    n = d["NODE"]
    print(f"{d['ops']:14s} {n:8d} | {cold:9.3f} {miss:6.3f} {cold-miss:8.3f} {1e9*(cold-miss)/n:7.0f} {d['pf']:7d} | {warm:9.3f} {1e9*warm/n:7.0f} {w['pf']:7d} | {cold-warm:9.3f} | {d['secs']:9.2f} {w['secs']:9.2f}")
    for j, v in enumerate([n, cold, miss, cold - miss, warm, cold - warm, d["secs"], w["secs"]]):
        tot[j] += v
print("TOTAL nodes %d cold %.2f miss %.2f hitpart %.2f warm %.2f cold-warm %.2f secs %.2f / %.2f" % tuple(tot))
