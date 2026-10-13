import bisect, collections, gzip, json, os, re, sys

# usage: prof_callers.py <dir> <key substring> [raw]: over the busy samples of <dir>/pcs.json.gz (samply, presymbolicated):
# inclusive shares of hc:: and hashbrown frames; for samples containing <key>, the first two caller frames above the outermost
# <key> frame (skipping hc::/hashbrown frames unless `raw`), the frames below it, and its leaf frames; all as % of busy samples
D = sys.argv[1]
KEY = sys.argv[2]
p = json.load(gzip.open(f"{D}/pcs.json.gz"))
syms = json.load(open(f"{D}/pcs.json.syms.json"))
ST = syms["string_table"]
tables = {lib["debug_name"]: sorted((e["rva"], e["size"], ST[e["symbol"]]) for e in lib["symbol_table"]) for lib in syms["data"]}
libs = p["libs"]
threads = list(p["threads"]) + [t for sp in p.get("processes", []) for t in sp["threads"]]
IDLE = ("NtWaitFor", "NtDelayExecution", "NtWaitForWorkViaWorkerFactory", "ZwWaitFor", "NtRemoveIoCompletion", "NtWaitForAlertByThreadId")


def short(s):
    while True:
        s2 = re.sub(r"<[^<>]*>", "", s)
        if s2 == s:
            return s[:110]
        s = s2


tot = 0
incl = collections.Counter()
c1, c2, leaf, below = collections.Counter(), collections.Counter(), collections.Counter(), collections.Counter()
keyed = 0
for t in threads:
    S, ft, fu, stt, rt = t["stringArray"], t["frameTable"], t["funcTable"], t["stackTable"], t.get("resourceTable")
    cache = {}

    def name(fr):
        if fr in cache:
            return cache[fr]
        f = ft["func"][fr]
        n = S[fu["name"][f]]
        m = re.match(r"^(?:fun_|0x)([0-9a-f]+)$", n)
        if m:
            rva = int(m.group(1), 16)
            res = fu["resource"][f]
            lib = libs[rt["lib"][res]]["debugName"] if res is not None and res >= 0 else None
            rows = tables.get(lib)
            n = f"{lib}:{n}"
            if rows:
                i = bisect.bisect_right(rows, (rva, 1 << 62, "")) - 1
                if i >= 0 and rva < rows[i][0] + max(rows[i][1], 1):
                    n = rows[i][2]
        cache[fr] = short(n)
        return cache[fr]

    for s in t["samples"]["stack"]:
        if s is None:
            continue
        chain = []
        while s is not None:
            chain.append(name(stt["frame"][s]))
            s = stt["prefix"][s]
        if any(chain[0].startswith(x) for x in IDLE):
            continue
        tot += 1
        for c in set(chain):
            if "hc::" in c or "hashbrown" in c:
                incl[c] += 1
        idx = [i for i, c in enumerate(chain) if KEY in c]
        if idx:
            keyed += 1
            above = [c for c in chain[idx[-1] + 1:] if len(sys.argv) > 3 or ("hc::" not in c and "hashbrown" not in c)]
            c1[above[0] if above else "-"] += 1
            leaf[chain[0]] += 1
            for c in set(chain[:idx[-1]]):
                below[c] += 1
            c2[" <- ".join(above[:2]) if above else "-"] += 1
print(f"busy samples {tot}; containing {KEY}: {keyed} ({100*keyed/tot:.1f}%)")
print("== INCL hc:: / hashbrown frames (% of busy)")
for n, v in incl.most_common(25):
    print(f"  {100*v/tot:5.1f}% {n}")
print(f"== first caller above {KEY} (% of busy)")
for n, v in c1.most_common(25):
    print(f"  {100*v/tot:5.1f}% {n}")
print(f"== two callers above {KEY} (% of busy)")
for n, v in c2.most_common(30):
    print(f"  {100*v/tot:5.1f}% {n}")
print(f"== inclusive below {KEY} (% of busy)")
for n, v in below.most_common(20):
    print(f"  {100*v/tot:5.1f}% {n}")
print(f"== leaf frames under {KEY} (% of busy)")
for n, v in leaf.most_common(20):
    print(f"  {100*v/tot:5.1f}% {n}")
