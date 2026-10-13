import bisect, collections, gzip, json, os, re, sys

# usage: prof_self.py <dir>: busy samples by leaf frame (self time), and by the first non-std, non-hashbrown frame
# the first two non-hc caller frames above the outermost <key> frame, by share of all busy samples
D = sys.argv[1]
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
leaf = collections.Counter(); own = collections.Counter()
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
        leaf[chain[0]] += 1
        own[next((c for c in chain if not re.match(r"^(core::|alloc::|std::|hashbrown::|ntdll|KERNEL|im::)", c)), chain[0])] += 1
print(f"busy samples {tot}")
print("== self (leaf frame)")
for n, v in leaf.most_common(30):
    print(f"  {100*v/tot:5.1f}% {n}")
print("== self, std/hashbrown/im frames charged to the first other frame")
for n, v in own.most_common(30):
    print(f"  {100*v/tot:5.1f}% {n}")
