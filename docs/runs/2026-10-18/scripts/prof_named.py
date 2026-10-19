# prof_named.py <dir> <exe>: self and inclusive busy-sample shares by function of a samply profile (pcs.json.gz) whose exe
# frames samply left as fun_<rva>: every sampled exe address is named with llvm-symbolizer against <exe>'s PDB (inlined
# frames expanded, image base 0x140000000). Prints the top self and inclusive functions (church_bv/tatic frames for
# inclusive) and writes the table to <dir>/named.txt.
# Run as `python -P prof_named.py <dir> <exe> < /dev/null`.
import collections, gzip, json, re, subprocess, sys

D, EXE = sys.argv[1], sys.argv[2]
p = json.load(gzip.open(f"{D}/pcs.json.gz"))
libs = p["libs"]
threads = list(p["threads"]) + [t for sp in p.get("processes", []) for t in sp["threads"]]
# PROF_THREAD=<name>: only threads of that name (e.g. search::rule_miner), the table in named_<name>.txt
ONLY = __import__("os").environ.get("PROF_THREAD")
threads = [t for t in threads if ONLY is None or t.get("name") == ONLY]
IDLE = ("NtWaitFor", "NtDelayExecution", "NtWaitForWorkViaWorkerFactory", "ZwWaitFor", "NtRemoveIoCompletion", "NtWaitForAlertByThreadId")
syms = json.load(open(f"{D}/pcs.json.syms.json"))
ST = syms["string_table"]
import bisect
tables = {lib["debug_name"]: sorted((e["rva"], e["size"], ST[e["symbol"]]) for e in lib["symbol_table"]) for lib in syms["data"]}

# per sample: list of frames, each (lib debugName, rva) or a name
samples = []
for t in threads:
    S, ft, fu, stt, rt = t["stringArray"], t["frameTable"], t["funcTable"], t["stackTable"], t.get("resourceTable")
    cache = {}

    def frame(fr):
        if fr in cache:
            return cache[fr]
        f = ft["func"][fr]
        res = fu["resource"][f]
        lib = libs[rt["lib"][res]]["debugName"] if rt is not None and res is not None and res >= 0 else None
        addr = ft["address"][fr] if "address" in ft else None
        n = S[fu["name"][f]]
        m = re.match(r"^(?:fun_|0x)([0-9a-f]+)$", n)
        out = None
        if lib and "church_bv" in lib.lower() or lib and "bv_prof" in lib.lower():
            rva = addr if addr is not None and addr >= 0 else (int(m.group(1), 16) if m else None)
            out = ("exe", rva)
        else:
            rows = tables.get(lib)
            if m and rows:
                rva = int(m.group(1), 16)
                i = bisect.bisect_right(rows, (rva, 1 << 62, "")) - 1
                if i >= 0 and rva < rows[i][0] + max(rows[i][1], 1):
                    n = rows[i][2]
            out = ("name", n)
        cache[fr] = out
        return out

    for s in t["samples"]["stack"]:
        if s is None:
            continue
        chain = []
        while s is not None:
            chain.append(frame(stt["frame"][s]))
            s = stt["prefix"][s]
        if chain[0][0] == "name" and chain[0][1].startswith(IDLE):
            continue
        samples.append(chain)

addrs = sorted({f[1] for c in samples for f in c if f[0] == "exe" and f[1] is not None})
inp = "\n".join(hex(0x140000000 + a) for a in addrs) + "\n"
r = subprocess.run(["llvm-symbolizer", "--obj=" + EXE, "--functions=linkage", "--demangle", "--inlining", "--no-untag-mte-tags"],
                   input=inp, capture_output=True, text=True)
if r.returncode != 0:
    r = subprocess.run(["llvm-symbolizer", "--obj=" + EXE, "--functions=linkage", "--demangle", "--inlining"], input=inp, capture_output=True, text=True)
blocks = r.stdout.strip("\n").split("\n\n")
assert len(blocks) == len(addrs), (len(blocks), len(addrs))


def short(s):
    while True:
        s2 = re.sub(r"<[^<>]*>", "", s)
        if s2 == s:
            break
        s = s2
    s = re.sub(r"::h[0-9a-f]{16}$", "", s)
    s = re.sub(r"\{\{closure\}\}", "{closure}", s)
    return s[:120]


# each address: its function names, innermost first (inlined frames expanded)
names = {}
for a, b in zip(addrs, blocks):
    ls = b.split("\n")
    names[a] = [short(ls[i]) for i in range(0, len(ls), 2)]

tot = len(samples)
selfc, incl = collections.Counter(), collections.Counter()
for c in samples:
    flat = []
    for f in c:
        if f[0] == "exe":
            flat.extend(names.get(f[1], [f"exe:{f[1]}"]))
        else:
            flat.append(f[1])
    selfc[flat[0]] += 1
    for n in set(flat):
        if re.match(r"^(church_bv|tatic)::", n):
            incl[n] += 1
lines = [f"busy samples {tot}", "== self (leaf, inlined frames expanded)"]
lines += [f"  {100*v/tot:5.1f}% {n}" for n, v in selfc.most_common(40)]
lines += ["== inclusive (church_bv/tatic frames)"]
lines += [f"  {100*v/tot:5.1f}% {n}" for n, v in incl.most_common(60)]
# optional leaf substrings: for samples whose leaf contains one, the first two church_bv/tatic frames above it
for key in sys.argv[3:]:
    by = collections.Counter()
    for c in samples:
        flat = []
        for f in c:
            flat.extend(names.get(f[1], [f"exe:{f[1]}"]) if f[0] == "exe" else [f[1]])
        if key in flat[0]:
            up = [n for n in flat[1:] if re.match(r"^(church_bv|tatic)::", n) and key not in n][:2]
            by[" < ".join(up)] += 1
    lines += [f"== callers of leaves matching {key!r}"] + [f"  {100*v/tot:5.1f}% {n}" for n, v in by.most_common(8)]
open(f"{D}/named" + (f"_{ONLY.replace(':', '_')}" if ONLY else "") + ".txt", "w").write("\n".join(lines) + "\n")
print("\n".join(lines))
