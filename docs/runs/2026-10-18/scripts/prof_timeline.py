# prof_timeline.py <dir>: where a samply profile's wall goes, by how many threads are busy at once. A sample is busy when
# its threadCPUDelta is at least half the interval. Threads are classed: the miner's main thread (`search::rule_miner`),
# other named threads (driver, workers), and unnamed threads of a process with a miner (its scoring pools).
# Run as `python -P prof_timeline.py <dir> < /dev/null`.
import collections, gzip, json, sys

p = json.load(gzip.open(sys.argv[1] + "/pcs.json.gz"))
print("sampleUnits", p["meta"].get("sampleUnits"))
iv = p["meta"]["interval"]
unit = (p["meta"].get("sampleUnits") or {}).get("threadCPUDelta", "µs")
scale = {"µs": 1000.0, "ns": 1e6, "variable CPU cycles": None}.get(unit, 1000.0)
threads = list(p["threads"]) + [t for sp in p.get("processes", []) for t in sp["threads"]]
miner_pids = {t.get("pid") for t in threads if t.get("name") == "search::rule_miner"}
busy = collections.defaultdict(lambda: collections.Counter())  # ms bucket -> class -> busy samples
t_min, t_max = 1e18, 0
for t in threads:
    s = t["samples"]
    name = t.get("name") or ""
    cls = "miner-main" if name == "search::rule_miner" else ("pool" if name.startswith("Thread <") and t.get("pid") in miner_pids else ("other:" + name if not name.startswith("Thread <") else "other-unnamed"))
    last = None
    for tm, cpu in zip(s["time"], s.get("threadCPUDelta") or [None] * len(s["time"])):
        dt = (tm - last) if last is not None else iv
        last = tm
        if cpu is None or scale is None:
            continue
        if cpu / scale >= 0.5 * min(dt, iv * 4):
            busy[int(tm)][cls] += 1
            t_min, t_max = min(t_min, tm), max(t_max, tm)
# per ms: busy thread count; histogram of wall by concurrency, and the busy samples by class at each concurrency
hist, by = collections.Counter(), collections.defaultdict(collections.Counter)
for ms in range(int(t_min), int(t_max) + 1):
    c = busy.get(ms, {})
    n = sum(c.values())
    hist[min(n, 8)] += 1
    for k, v in c.items():
        by[min(n, 8)][k] += v
wall = sum(hist.values())
print(f"span {wall/1000:.1f} s, busy samples {sum(sum(c.values()) for c in busy.values())}")
for n in sorted(hist):
    top = ", ".join(f"{k} {v}" for k, v in by[n].most_common(4))
    print(f"{n}{'+' if n == 8 else ''} busy: {hist[n]/1000:6.1f} s wall ({100*hist[n]/wall:4.1f}%)  {top}")
# per second: cores busy
print("per second (cores):", " ".join(f"{sum(sum(busy.get(ms, {}).values()) for ms in range(s0, s0 + 1000))/1000:.1f}" for s0 in range(int(t_min), int(t_max), 1000)))
