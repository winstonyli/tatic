import re
import sys

# usage: an6.py <run id> <L> [stride]: cold (pass 1) totals only, for runs without a repeat
run, L = sys.argv[1], int(sys.argv[2])
stride = int(sys.argv[3]) if len(sys.argv) > 3 else 1
base = r"C:\Users\Winston Li\AppData\Local\claude-runs\tatic" + "\\" + run + r"\out.log"
hz = None
tot = dict(nodes=0, norm=0, miss=0, secs=0, pf=0, lk=0, ev=0, ins=0, prn=0, n=0)
for line in open(base, encoding="utf-8", errors="replace"):
    if line.startswith("NP HZ"):
        hz = float(line.split()[2])
    m = re.match(r"NP pass=(\d+) salt=(\d+) L=(\d+) i=(\d+) ops=(\S+) laws=(\d+) same=(\w+) secs=([\d.]+) pf=(\d+) private_mb=(\d+) ws_mb=(\d+) ?(.*)", line.strip())
    if not m or int(m[1]) != 1 or int(m[3]) != L or int(m[4]) % stride:
        continue
    d = {}
    for kv in m[12].split():
        k, v = kv.split("=")
        d[k] = int(v)
    tot["nodes"] += d.get("NODE", 0)
    tot["norm"] += d.get("NORM_T", 0)
    tot["lk"] += d.get("LK_MISS_T", 0)
    tot["ev"] += d.get("V_EVAL_T", 0)
    tot["ins"] += d.get("V_INS_T", 0)
    tot["prn"] += d.get("V_PRINT_T", 0)
    tot["secs"] += float(m[8])
    tot["pf"] += int(m[9])
    tot["n"] += 1
miss = (tot["lk"] + tot["ev"] + tot["ins"]) / hz
norm = tot["norm"] / hz
print(f"L={L} stride {stride}: {tot['n']} streams, {tot['nodes']/1e6:.2f} M nodes, build {tot['secs']:.2f} s, normalize {norm:.2f} s ({100*norm/tot['secs']:.1f}% of build), misses {miss:.2f} s ({100*miss/tot['secs']:.1f}% of build; lookup {tot['lk']/hz:.2f}, verdict eval {tot['ev']/hz:.2f}, insert+print {tot['ins']/hz:.2f} of which print {tot['prn']/hz:.2f}), hit part {norm-miss:.2f} s = {1e9*(norm-miss)/tot['nodes']:.0f} ns/node, faults {tot['pf']}")
