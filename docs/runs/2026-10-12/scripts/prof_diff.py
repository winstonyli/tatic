import bisect, collections, gzip, json, os, re, subprocess, sys

# usage: prof_diff.py <dirA> <startA> <endA> <unitsA> <dirB> <startB> <endB> <unitsB>
# Two samply profiles (presymbolicated, <dir>/pcs.json.gz + pcs.json.syms.json), each cut to busy samples between two
# wall-clock marks (Unix ms, as a probe prints them), compared per unit of work (e.g. new table entries): each function's
# self time per unit in A and in B, and the difference, largest first. Self time is by leaf frame, and also with std,
# alloc, core, hashbrown and ntdll frames charged to the first other frame. With PROF_EXE=<exe>, names samply left as
# fun_<rva> are resolved with llvm-symbolizer (the PDB must sit beside the exe under the name the exe records).
IDLE = ("NtWaitFor", "NtDelayExecution", "NtWaitForWorkViaWorkerFactory", "ZwWaitFor", "NtRemoveIoCompletion", "NtWaitForAlertByThreadId")


def short(s):
    while True:
        s2 = re.sub(r"<[^<>]*>", "", s)
        if s2 == s:
            return s[:90]
        s = s2


def load(d, start, end):
    p = json.load(gzip.open(f"{d}/pcs.json.gz"))
    syms = json.load(open(f"{d}/pcs.json.syms.json"))
    st = syms["string_table"]
    tables = {lib["debug_name"]: sorted((e["rva"], e["size"], st[e["symbol"]]) for e in lib["symbol_table"]) for lib in syms["data"]}
    libs, t0 = p["libs"], p["meta"]["startTime"]
    threads = list(p["threads"]) + [t for sp in p.get("processes", []) for t in sp["threads"]]
    leaf, own, busy, interval = collections.Counter(), collections.Counter(), 0, p["meta"]["interval"]
    for t in threads:
        s_, ft, fu, stt, rt = t["stringArray"], t["frameTable"], t["funcTable"], t["stackTable"], t.get("resourceTable")
        cache = {}

        def name(fr):
            if fr in cache:
                return cache[fr]
            f = ft["func"][fr]
            n = s_[fu["name"][f]]
            m = re.match(r"^(?:fun_|0x)([0-9a-f]+)$", n)
            if m:
                rva, res = int(m.group(1), 16), fu["resource"][f]
                lib = libs[rt["lib"][res]]["debugName"] if res is not None and res >= 0 else None
                rows = tables.get(lib)
                n = f"{lib}:{n}"
                if rows:
                    i = bisect.bisect_right(rows, (rva, 1 << 62, "")) - 1
                    if i >= 0 and rva < rows[i][0] + max(rows[i][1], 1):
                        n = rows[i][2]
            cache[fr] = short(n)
            return cache[fr]

        sm = t["samples"]
        times = sm.get("time")
        if times is None:
            times, acc = [], 0.0
            for dt in sm["timeDeltas"]:
                acc += dt
                times.append(acc)
        for s, tm in zip(sm["stack"], times):
            if s is None or not (start <= t0 + tm <= end):
                continue
            chain = []
            while s is not None:
                chain.append(name(stt["frame"][s]))
                s = stt["prefix"][s]
            if any(chain[0].startswith(x) for x in IDLE):
                continue
            busy += 1
            leaf[chain[0]] += 1
            own[next((c for c in chain if not re.match(r"^(core::|alloc::|std::|hashbrown::|ntdll|KERNEL)", c)), chain[0])] += 1
    return busy, interval, leaf, own


def symbolize(profiles, exe):
    # names samply left as `fun_<rva>` (its symbol table missed them), resolved against `exe` and the PDB beside it
    # under the name the exe records; samples are re-keyed by function, merging names that resolve alike
    raw = sorted({f for P in profiles for k in (2, 3) for f in P[k] if re.match(r"^fun_[0-9a-f]+$", f)})
    if not raw:
        return profiles
    q = "".join(f"0x{0x140000000 + int(f[4:], 16):x}\n" for f in raw)
    out = subprocess.run(["llvm-symbolizer", f"--obj={exe}", "--functions=linkage", "--no-inlines"], input=q, capture_output=True, text=True).stdout
    names = [b.splitlines()[0] for b in out.strip().split("\n\n")]
    m = {f: (short(n) if n != "??" else f) for f, n in zip(raw, names)}
    res = []
    for busy, iv, leaf, own in profiles:
        def re_key(c):
            r = collections.Counter()
            for f, v in c.items():
                r[m.get(f, f)] += v
            return r
        res.append((busy, iv, re_key(leaf), re_key(own)))
    return res


a = sys.argv[1:5]
b = sys.argv[5:9]
A = load(a[0], float(a[1]), float(a[2]))
B = load(b[0], float(b[1]), float(b[2]))
if os.environ.get("PROF_EXE"):
    A, B = symbolize([A, B], os.environ["PROF_EXE"])
ua, ub = float(a[3]), float(b[3])
for (busy, iv, _, _), u, tag in ((A, ua, "A"), (B, ub, "B")):
    print(f"{tag}: busy samples {busy}, interval {iv} ms, {busy * iv * 1e6 / u:.0f} ns busy per unit")
for k, title in ((2, "leaf frame"), (3, "first non-std frame")):
    print(f"== self ns per unit, by {title}: A, B, B - A (largest differences first)")
    ns = lambda P, u, f: P[k][f] * P[1] * 1e6 / u
    keys = set(A[k]) | set(B[k])
    rows = sorted(keys, key=lambda f: -(ns(B, ub, f) - ns(A, ua, f)))
    for f in rows[:25]:
        print(f"  {ns(A, ua, f):7.1f} {ns(B, ub, f):7.1f} {ns(B, ub, f) - ns(A, ua, f):+7.1f}  {f}")
    print("  ... smallest:")
    for f in rows[-5:]:
        print(f"  {ns(A, ua, f):7.1f} {ns(B, ub, f):7.1f} {ns(B, ub, f) - ns(A, ua, f):+7.1f}  {f}")
