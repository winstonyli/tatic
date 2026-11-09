"""Per-function time of one check from prof.sh's traces. Reads each d<N>.profile.txt (prof_report.sh) and d<N>.log in the
run folders given as arguments and keeps the tatic test process's rows. Each d needs two traces with different numbers
of checks: a check's cost is their difference over the difference in checks, so the process's one-off costs (start,
build, its 256 MB stack, exit) cancel. Prints the one-off and ns per unit of kernel work (statement build and check) by
module at each d, then the excess of the largest d over the smallest and over the next largest (its ms per check less
the smaller d's scaled by the work ratio, over every function seen at either), largest first.
Run: python -P prof_agg.py <run folder>... < /dev/null"""
import collections, glob, os, re, sys

ROW = re.compile(r"^\s*(.+?)\s*\(\s*(\d+)\),\s*(\d+),\s*([\d.]+),\s*(.+?)\s*$")
traces = collections.defaultdict(list)  # d -> [(checks, work per check, Counter of function -> total ms)]
for run in sys.argv[1:]:
    for prof in glob.glob(os.path.join(run, "d*.profile.txt")):
        d = int(re.search(r"d(\d+)\.profile", prof).group(1))
        works = re.findall(r"work=(\d+)", open(prof.replace(".profile.txt", ".log"), encoding="utf-8").read())
        fn = collections.Counter()
        for line in open(prof, encoding="utf-8", errors="replace"):
            x = ROW.match(line)
            if x and x.group(1).lower().startswith("tatic-"):
                fn[x.group(5)] += int(x.group(3)) / 1000
        traces[d].append((len(works), int(works[0]), fn))
per = {}  # d -> (work per check, {function: ms per check}, one-off ms)
for d, ts in traces.items():
    (n0, w, f0), (n1, _, f1) = min(ts, key=lambda t: t[0]), max(ts, key=lambda t: t[0])
    assert n1 > n0, f"d{d} needs two traces with different numbers of checks"
    check = {k: (f1.get(k, 0) - f0.get(k, 0)) / (n1 - n0) for k in set(f0) | set(f1)}
    per[d] = (w, check, sum(f0.values()) - n0 * sum(check.values()))
ds = sorted(per)
short = lambda k: k.split("!")[-1][-60:]
print("checks per trace:", "  ".join(f"d{d} {sorted(t[0] for t in traces[d])}" for d in ds))
print("one-off ms per process:", "  ".join(f"d{d} {per[d][2]:.0f}" for d in ds))
print("ms per check:", "  ".join(f"d{d} {sum(per[d][1].values()):.1f}" for d in ds))
print("ns per unit of work:", "  ".join(f"d{d} {1e6 * sum(per[d][1].values()) / per[d][0]:.0f}" for d in ds))
mods = collections.Counter()
for d in ds:
    for k, v in per[d][1].items():
        mods[k.split("!")[0]] += v
print("\nmodule" + "".join(f"{'d' + str(d):>8}" for d in ds), "(ns per unit of work)")
for m, _ in mods.most_common(4):
    print(f"{m[:24]:24}" + "".join(f"{1e6 * sum(v for k, v in per[d][1].items() if k.split('!')[0] == m) / per[d][0]:8.1f}" for d in ds))
for a in [ds[0]] + ([ds[-2]] if len(ds) > 2 else []):
    b = ds[-1]
    (wa, fa, _), (wb, fb, _) = per[a], per[b]
    r = wb / wa
    ex = {k: fb.get(k, 0) - r * fa.get(k, 0) for k in set(fa) | set(fb)}
    tot = sum(ex.values())
    print(f"\nd{a} -> d{b}: work x{r:.3f}, time x{sum(fb.values()) / sum(fa.values()):.3f}, excess {tot:.1f} ms of {sum(fb.values()):.1f} per check")
    print(f"{'function':60} {'ns/w d' + str(a):>9} {'ns/w d' + str(b):>9} {'excess ms':>9} {'share':>6}")
    for k, v in sorted(ex.items(), key=lambda kv: -kv[1])[:22]:
        print(f"{short(k):60} {1e6 * fa.get(k, 0) / wa:9.2f} {1e6 * fb.get(k, 0) / wb:9.2f} {v:9.2f} {100 * v / tot:5.1f}%")
    kx = sum(v for k, v in ex.items() if k.startswith("ntoskrnl"))
    print(f"{'(all of ntoskrnl.exe)':60} {'':9} {'':9} {kx:9.2f} {100 * kx / tot:5.1f}%")
