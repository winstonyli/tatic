import json, sys
# sw_diff.py <a> <b>: functions whose CPU (µs, from sw_where.py's <dir>/counts.json) changed most between two profiles,
# self and inclusive. Symbols differ where the builds inline differently ("Samples are not CPU" in docs/tier-cycle.md).
a, b = (json.load(open(f"{d}/counts.json")) for d in sys.argv[1:3])
for kind in ("self", "incl"):
    keys = set(a[kind]) | set(b[kind])
    d = sorted(keys, key=lambda k: b[kind].get(k, 0) - a[kind].get(k, 0))
    print(f"== {kind}: tot {a['tot']} -> {b['tot']}; largest rises")
    for k in d[::-1][:25]:
        print(f"  {a[kind].get(k,0):6d} -> {b[kind].get(k,0):6d}  {k[:100]}")
    print(f"== {kind}: largest falls")
    for k in d[:15]:
        print(f"  {a[kind].get(k,0):6d} -> {b[kind].get(k,0):6d}  {k[:100]}")
