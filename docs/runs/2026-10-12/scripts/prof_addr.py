import bisect, collections, gzip, json, re, sys

# usage: prof_addr.py <dir> <name substring>: leaf-sample instruction addresses (rva) inside functions whose name contains
# the substring, most sampled first, for llvm-symbolizer (address = image base + rva)
D, KEY = sys.argv[1], sys.argv[2]
p = json.load(gzip.open(f"{D}/pcs.json.gz"))
syms = json.load(open(f"{D}/pcs.json.syms.json"))
ST = syms["string_table"]
tables = {lib["debug_name"]: sorted((e["rva"], e["size"], ST[e["symbol"]]) for e in lib["symbol_table"]) for lib in syms["data"]}
libs = p["libs"]
threads = list(p["threads"]) + [t for sp in p.get("processes", []) for t in sp["threads"]]
hits = collections.Counter()
tot = 0
for t in threads:
    S, ft, fu, stt, rt = t["stringArray"], t["frameTable"], t["funcTable"], t["stackTable"], t.get("resourceTable")
    for s in t["samples"]["stack"]:
        if s is None:
            continue
        fr = stt["frame"][s]
        f = ft["func"][fr]
        n = S[fu["name"][f]]
        addr = ft["address"][fr]
        res = fu["resource"][f]
        lib = libs[rt["lib"][res]]["debugName"] if res is not None and res >= 0 else None
        rows = tables.get(lib)
        if rows:
            i = bisect.bisect_right(rows, (addr, 1 << 62, "")) - 1
            if i >= 0 and addr < rows[i][0] + max(rows[i][1], 1):
                n = rows[i][2]
        if KEY in n:
            tot += 1
            hits[addr] += 1
print(f"samples {tot}")
for a, v in hits.most_common(25):
    print(f"0x{0x140000000 + a:x} {v}")
