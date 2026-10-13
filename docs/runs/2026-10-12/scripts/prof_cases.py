import bisect, collections, gzip, json, os, re, sys

# proof_cost_split profile: busy samples (idle leaves dropped), inclusive shares overall and under one scope (argv[1], default shared_lemma)
D = os.path.dirname(os.path.abspath(__file__)) + "/prof11"
p = json.load(gzip.open(f"{D}/pcs.json.gz"))
syms = json.load(open(f"{D}/pcs.json.syms.json"))
ST = syms["string_table"]
tables = {lib["debug_name"]: sorted((e["rva"], e["size"], ST[e["symbol"]]) for e in lib["symbol_table"]) for lib in syms["data"]}
libs = p["libs"]
SCOPE = sys.argv[1] if len(sys.argv) > 1 else "shared_lemma"
threads = list(p["threads"]) + [t for sp in p.get("processes", []) for t in sp["threads"]]
IDLE = ("NtWaitFor", "NtDelayExecution", "NtWaitForWorkViaWorkerFactory", "ZwWaitFor", "NtRemoveIoCompletion")


def short(s):
    while True:
        s2 = re.sub(r"<[^<>]*>", "", s)
        if s2 == s:
            return s[:110]
        s = s2


tot = 0
incl, scoped_incl, scoped_self = collections.Counter(), collections.Counter(), collections.Counter()
scoped = 0
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
            incl[c] += 1
        # the part of the chain below the outermost SCOPE frame
        idx = [i for i, c in enumerate(chain) if SCOPE in c]
        if idx:
            scoped += 1
            below = chain[: idx[-1]]
            for c in set(below):
                scoped_incl[c] += 1
            scoped_self[chain[0]] += 1
print(f"busy samples {tot}; under {SCOPE}: {scoped} ({100*scoped/tot:.1f}%)")
keep = lambda n: any(x in n for x in ("church_bv", "tatic", "alloc", "hash", "Hash", "memcpy", "memmove", "drop"))
print("== INCL (all)")
for n, v in [kv for kv in incl.most_common() if keep(kv[0])][:40]:
    print(f"  {100*v/tot:5.1f}% {n}")
print(f"== INCL below {SCOPE} (% of {SCOPE})")
for n, v in [kv for kv in scoped_incl.most_common() if keep(kv[0])][:45]:
    print(f"  {100*v/scoped:5.1f}% {n}")
print(f"== SELF under {SCOPE}")
for n, v in scoped_self.most_common(25):
    print(f"  {100*v/scoped:5.1f}% {n}")
