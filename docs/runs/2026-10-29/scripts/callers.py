# callers.py <dir> <exe> <frame>... [--with <frame>...] [--without <frame>...]: the busy samples of a samply profile
# (pcs.json.gz, frames named as by docs/runs/2026-10-18/scripts/prof_named.py, whose loader this runs) that contain any
# of the given frames (prefix match), and also any `--with` frame and no `--without` frame: their union share, then that
# share split by the nearest church_bv frame outside the outermost match (the caller). Shares are of all busy samples.
# Run as `python -P callers.py <dir> <exe> <frame>... < /dev/null`.
import collections, os, sys

here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, "..", "..", "2026-10-18", "scripts", "prof_named.py")).read()
exec(compile(src[: src.index("tot = len(samples)")], "prof_named.py", "exec"))

sets, mode = {"keys": [], "--with": [], "--without": []}, "keys"
for a in sys.argv[3:]:
    if a in sets:
        mode = a
    else:
        sets[mode].append(a)
keys, need, skip = (tuple(sets[k]) for k in ("keys", "--with", "--without"))
tot, c, u = len(samples), collections.Counter(), 0
for ch in samples:
    flat = [n for f in ch for n in (names.get(f[1], [f"exe:{f[1]}"]) if f[0] == "exe" else [f[1]])]
    hits = [i for i, n in enumerate(flat) if n.startswith(keys)]
    if not hits:
        continue
    if need and not any(n.startswith(need) for n in flat) or skip and any(n.startswith(skip) for n in flat):
        continue
    u += 1
    out = next((n for n in flat[max(hits) + 1:] if n.startswith("church_bv::") and not n.startswith(keys)), "(none)")
    c[out] += 1
print(f"union {100 * u / tot:.2f}%")
for n, v in c.most_common(12):
    print(f"{100 * v / tot:6.2f}% {n}")
