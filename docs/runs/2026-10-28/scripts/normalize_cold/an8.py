import re
import sys

# usage: an8.py <run id>...: first-ask counts of the 14 streams (i%4==0) at L=4, pass 1, per run
for run in sys.argv[1:]:
    base = r"C:\Users\Winston Li\AppData\Local\claude-runs\tatic" + "\\" + run + r"\out.log"
    t = dict(LK_MISS=0, V_MISS=0, TE_SEARCH=0, BW_N=0)
    for line in open(base, encoding="utf-8", errors="replace"):
        m = re.match(r"NP pass=(\d+) salt=(\d+) L=(\d+) i=(\d+) ops=(\S+) laws=(\d+) same=(\w+) secs=([\d.]+) pf=(\d+) private_mb=(\d+) ws_mb=(\d+) ?(.*)", line.strip())
        if not m or int(m[1]) != 1 or int(m[3]) != 4 or int(m[4]) % 4:
            continue
        for kv in m[12].split():
            k, v = kv.split("=")
            if k in t:
                t[k] += int(v)
    print(run, t)
