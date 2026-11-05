# an1.py <run>: the NP rows of the run's out.log (normalize-cold probe) summed per level L and pass: build seconds, miss time by part, counts.
import re
import sys

run = sys.argv[1]
base = r"C:\Users\Winston Li\AppData\Local\claude-runs\tatic" + "\\" + run + r"\out.log"
rows = []
hz = None
for line in open(base, encoding="utf-8", errors="replace"):
    if line.startswith("NP HZ"):
        hz = float(line.split()[2])
    m = re.match(r"NP pass=(\d+) salt=(\d+) L=(\d+) i=(\d+) ops=(\S+) laws=(\d+) same=(\w+) secs=([\d.]+) pf=(\d+) private_mb=(\d+) ws_mb=(\d+) ?(.*)", line.strip())
    if not m:
        continue
    d = dict(pass_=int(m[1]), salt=int(m[2]), L=int(m[3]), i=int(m[4]), ops=m[5], laws=int(m[6]), same=m[7], secs=float(m[8]), pf=int(m[9]), priv=int(m[10]))
    for kv in m[12].split():
        k, v = kv.split("=")
        d[k] = int(v)
    rows.append(d)
print("rows", len(rows), "hz", hz)


def sec(d, k):
    return d.get(k, 0) / hz


def agg(sel, keys):
    return {k: sum(r.get(k, 0) for r in sel) for k in keys}


T = ["LK_MISS_T", "LK_VAL_T", "V_EVAL_T", "V_INS_T", "VB_T", "VT_T", "TE_SEARCH_T", "BW_EXH_T", "BW_AGREE_T", "NORM_T"]
N = ["NODE", "NODE_OP", "LK_ASK", "LK_NOVAR", "LK_MISS", "LK_FILLED", "LK_SOME", "LK_REPNE", "STEP_REP", "STEP_KVAR", "V_HIT", "V_MISS", "VB_N", "VB_SOME", "VT_N", "VT_SOME", "BW_N", "TE_CALL", "TE_PLAUS", "TE_PARSE", "TE_LAST", "TE_CAP", "TE_HIT", "TE_SEARCH", "TE_SEARCH_SOME", "NORM_LAWS", "pf", "laws"]
for L in sorted({r["L"] for r in rows}):
    for sub, idx in (("14 streams (i%4==0)", lambda r: r["i"] % 4 == 0), ("all 56", lambda r: True)):
        print(f"\n=== L={L}, {sub}")
        for p in sorted({r["pass_"] for r in rows}):
            sel = [r for r in rows if r["L"] == L and r["pass_"] == p and idx(r)]
            if not sel:
                continue
            t = agg(sel, T)
            n = agg(sel, N)
            secs = sum(r["secs"] for r in sel)
            print(f"pass {p} ({len(sel)} streams): build secs {secs:.2f}; NORM_T {t['NORM_T']/hz:.3f}s")
            print("   miss time: lookup miss %.3f (values %.3f) | verdict eval %.3f (bitwise %.3f [exh %.3f agree %.3f], tree %.3f [search %.3f]) | verdict insert+print %.3f" % (t["LK_MISS_T"]/hz, t["LK_VAL_T"]/hz, t["V_EVAL_T"]/hz, t["VB_T"]/hz, t["BW_EXH_T"]/hz, t["BW_AGREE_T"]/hz, t["VT_T"]/hz, t["TE_SEARCH_T"]/hz, t["V_INS_T"]/hz))
            print("   counts:", {k: v for k, v in n.items() if v})
