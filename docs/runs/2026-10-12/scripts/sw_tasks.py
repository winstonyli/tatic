import gzip, json, sys, collections
# sw_tasks.py <old> <new>: CPU per sweep child, matched by order. <old>: one sw.exe process per child (the driver is the
# process with a driver::sweep thread). <new>: one worker process; a task is a thread named after a test, plus the threads
# registered while it ran. CPU is the sum of threadCPUDelta (µs), printed in ms. docs/tier-cycle.md, "Samples are not CPU".
def load(d):
    p = json.load(gzip.open(f"{d}/sw.json.gz"))
    return [t for pr in [p] + p.get("processes", []) for t in pr["threads"] if t.get("processName") == "sw.exe"]
cpu = lambda t: sum(x or 0 for x in t["samples"].get("threadCPUDelta") or [])
def old(d):
    th = load(d); bypid = collections.defaultdict(list)
    for t in th: bypid[t["pid"]].append(t)
    out = []
    for pid, ts in bypid.items():
        names = [t["name"] for t in ts if "::" in t["name"] and t["name"] != "driver::sweep"]
        if any(t["name"] == "driver::sweep" for t in ts) or not names: continue
        out.append((min(t["registerTime"] for t in ts), names[0], sum(cpu(t) for t in ts)))
    return [x[1:] for x in sorted(out)]
def new(d):
    th = load(d)
    wk = [t for t in th if t["name"] == "driver::worker"][0]["pid"]
    ts = [t for t in th if t["pid"] == wk]
    mains = sorted((t for t in ts if "::" in t["name"] and t["name"] != "driver::worker"), key=lambda t: t["registerTime"])
    # a task's main thread is the one named after the test with the earliest start within its window
    tasks, used = [], set()
    for m in mains:
        if m["tid"] in used: continue
        lo, hi = m["registerTime"], m["unregisterTime"]
        mine = [t for t in ts if lo <= t["registerTime"] <= hi and t["tid"] not in used]
        used |= {t["tid"] for t in mine}
        tasks.append((m["name"], sum(cpu(t) for t in mine)))
    return tasks
a, b = old(sys.argv[1]), new(sys.argv[2])
print(f"old children {len(a)}, new tasks {len(b)}; names agree: {[x[0] for x in a] == [x[0] for x in b]}")
n = min(len(a), len(b)); thirds = [range(0, n // 3), range(n // 3, 2 * n // 3), range(2 * n // 3, n)]
for kind in sorted({x[0] for x in a}):
    for k, r in enumerate(thirds):
        A = sum(a[i][1] for i in r if a[i][0] == kind); B = sum(b[i][1] for i in r if b[i][0] == kind)
        if A: print(f"  {kind:32s} third {k}: old {A/1e3:9.0f} new {B/1e3:9.0f} ratio {B/A:5.2f}")
A = sum(x[1] for x in a[:n]); B = sum(x[1] for x in b[:n]); print(f"all: old {A/1e3:.0f} ms new {B/1e3:.0f} ms ratio {B/A:.2f}")
