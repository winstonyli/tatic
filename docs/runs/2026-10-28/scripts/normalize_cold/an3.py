import re
import sys

# usage: an3.py <run id> <warm pass> [L] ; cold = pass 1, warm = the given pass (0 = immediate repeat, 2 = second sweep)
run = sys.argv[1]
wp = int(sys.argv[2])
L = int(sys.argv[3]) if len(sys.argv) > 3 else 4
stride = int(sys.argv[4]) if len(sys.argv) > 4 else 1
base = r"C:\Users\Winston Li\AppData\Local\claude-runs\tatic" + "\\" + run + r"\out.log"
hz = None
rows = []
for line in open(base, encoding="utf-8", errors="replace"):
    if line.startswith("NP HZ"):
        hz = float(line.split()[2])
    m = re.match(r"NP pass=(\d+) salt=(\d+) L=(\d+) i=(\d+) ops=(\S+) laws=(\d+) same=(\w+) secs=([\d.]+) pf=(\d+) private_mb=(\d+) ws_mb=(\d+) ?(.*)", line.strip())
    if not m:
        continue
    d = dict(pass_=int(m[1]), salt=int(m[2]), L=int(m[3]), i=int(m[4]), ops=m[5], secs=float(m[8]), pf=int(m[9]))
    for kv in m[12].split():
        k, v = kv.split("=")
        d[k] = int(v)
    rows.append(d)
print(f"{'stream':14s} {'nodes':>8s} | {'cold':>6s} {'miss':>6s} {'hit':>6s} {'ns/n':>5s} {'pf':>7s} | {'warm':>6s} {'ns/n':>5s} {'pf':>7s} | {'c-w':>6s} | {'cold s':>6s} {'warm s':>6s}")
tot = [0.0] * 8
for c in rows:
    if c["pass_"] != 1 or c["L"] != L or c["i"] % stride:
        continue
    w = [x for x in rows if x["pass_"] == wp and x["L"] == L and x["i"] == c["i"] and x["salt"] == c["salt"]]
    if not w:
        continue
    w = w[0]
    miss = (c.get("LK_MISS_T", 0) + c.get("V_EVAL_T", 0) + c.get("V_INS_T", 0)) / hz
    cold = c.get("NORM_T", 0) / hz
    warm = w.get("NORM_T", 0) / hz
    n = max(c.get("NODE", 0), 1)
    print(f"{c['ops']:14s} {n:8d} | {cold:6.3f} {miss:6.3f} {cold-miss:6.3f} {1e9*(cold-miss)/n:5.0f} {c['pf']:7d} | {warm:6.3f} {1e9*warm/n:5.0f} {w['pf']:7d} | {cold-warm:6.3f} | {c['secs']:6.2f} {w['secs']:6.2f}")
    for j, v in enumerate([n, cold, miss, cold - miss, warm, cold - warm, c["secs"], w["secs"]]):
        tot[j] += v
print("TOTAL nodes %d cold %.2f miss %.2f hitpart %.2f warm %.2f cold-warm %.2f secs %.2f / %.2f" % tuple(tot))
