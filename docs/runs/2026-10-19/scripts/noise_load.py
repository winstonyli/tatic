# For every runs.tsv: each arm against the first, per round; residual of the diff around its order's mean (clean
# rounds' mean), as % of the first arm's job CPU, binned by the round's highest other_pct.
import csv, glob, math, os, sys
root = os.path.expandvars(r"%LOCALAPPDATA%\claude-runs\tatic")
bins = [(0, 10), (10, 20), (20, 30), (30, 50), (50, 101)]
res = {b: [] for b in bins}
for tsv in glob.glob(root + r"\**\runs.tsv", recursive=True):
    rows = list(csv.DictReader(open(tsv, encoding="utf-8", errors="replace"), delimiter="\t"))
    if not rows or "position" not in rows[0]:
        continue
    arms = list(dict.fromkeys(r["arm"] for r in rows))
    if len(arms) < 2:
        continue
    by = {(r["arm"], r["round"]): r for r in rows}
    rounds = sorted({r["round"] for r in rows}, key=int)
    for arm in arms[1:]:
        pts = []
        for rd in rounds:
            a, b = by.get((arms[0], rd)), by.get((arm, rd))
            if not a or not b or a["exit"] != "0" or b["exit"] != "0":
                continue
            base = float(a["jobcpu_s"])
            d = 100 * (float(b["jobcpu_s"]) - base) / base
            load = max(float(a["other_pct"]), float(b["other_pct"]))
            clean = a["clean"] == "true" and b["clean"] == "true"
            pts.append((int(b["position"]) < int(a["position"]), d, load, clean))
        for first in (True, False):
            cl = [p[1] for p in pts if p[0] == first and p[3]]
            if len(cl) < 2:
                continue
            m = sum(cl) / len(cl)
            for p in pts:
                if p[0] == first:
                    e = p[1] - m
                    for b in bins:
                        if b[0] <= p[2] < b[1]:
                            res[b].append(e)
for b in bins:
    v = res[b]
    if v:
        print(f"others {b[0]:>2}-{b[1]:<3}% n={len(v):>3} rms {math.sqrt(sum(x*x for x in v)/len(v)):.2f}%  max |e| {max(abs(x) for x in v):.2f}%")
