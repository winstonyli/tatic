# prof_incl.py <dir> [<leaf prefix>]: busy samples of a samply profile (pcs.json.gz + pcs.json.syms.json, as profile.ps1
# writes them) by inclusive frame (each frame once per sample), church_bv/tatic frames only; then, for samples whose leaf
# starts with <leaf prefix> (default church_bv::rewrite::Term::op), the first caller frame that is not the leaf itself.
# Run as `python -P prof_incl.py <dir> < /dev/null`.
import bisect, collections, gzip, json, re, sys

D = sys.argv[1]
LEAF = sys.argv[2] if len(sys.argv) > 2 else "church_bv::rewrite::Term::op"
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
            return re.sub(r"\(.*", "", s)[:100]
        s = s2


tot, leafn = 0, 0
incl = collections.Counter(); caller = collections.Counter()
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
        incl.update({c for c in chain if c.startswith(("church_bv::", "tatic::"))})
        if chain[0].startswith(LEAF):
            leafn += 1
            caller[next((c for c in chain[1:] if not c.startswith(LEAF)), "?")] += 1
print(f"busy samples {tot}")
print("== inclusive (church_bv/tatic frames)")
for n, v in incl.most_common(40):
    print(f"  {100*v/tot:5.1f}% {n}")
print(f"== callers of {LEAF} ({100*leafn/tot:.1f}% of busy samples), share of all busy samples")
for n, v in caller.most_common(15):
    print(f"  {100*v/tot:5.1f}% {n}")
