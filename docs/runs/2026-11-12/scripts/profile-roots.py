# profile-roots.py <dir> <publics.txt>: the main thread's busy samples by root kind (thread start, other ntdll root, truncated
# at 256 frames), and within each, how many stacks hold the gate's build, the kernel check (encoding::holds), any
# tatic_kernel frame, a stacker segment, or compile_verify_and_apply. Exe frames named from the PDB's public symbols
# (nearest function at or below the address; enough for substring tests on mangled names; inlined frames such as
# compile_verify_and_apply and holds do not show, so their counts read 0).
# Run as `llvm-pdbutil dump --publics <exe>.pdb > publics.txt`, then
# `python -P profile-roots.py <dir> publics.txt < /dev/null` (g1, doc 28's cold paragraph).
import bisect, collections, gzip, json, re, sys
D, PUB = sys.argv[1], sys.argv[2]
syms, cur = [], None
for line in open(PUB, encoding="utf-8", errors="replace"):
    m = re.search(r"S_PUB32 \[size = \d+\] `(.*)`", line)
    if m: cur = m.group(1); continue
    m = re.search(r"flags = function, addr = 0001:(\d+)", line)
    if m and cur: syms.append((0x1000 + int(m.group(1)), cur)); cur = None
syms.sort(); addrs = [a for a, _ in syms]
def name(rva):
    i = bisect.bisect_right(addrs, rva) - 1
    return syms[i][1] if i >= 0 else "?"
p = json.load(gzip.open(f"{D}/pcs.json.gz"))
libs = p["libs"]
threads = [t for t in list(p["threads"]) + [t for sp in p.get("processes", []) for t in sp["threads"]] if t.get("name", "").startswith("execution")]
IDLE = ("NtWaitFor", "NtDelayExecution", "NtWaitForWorkViaWorkerFactory", "ZwWaitFor", "NtRemoveIoCompletion", "NtWaitForAlertByThreadId")
KEYS = {"cva": "compile_verify_and_apply", "build": "4gate5build", "holds": "8encoding5holds", "kernel": "12tatic_kernel", "segment": "10on_segment", "criterion": "9criterion", "instantiate": "11instantiate"}
g = collections.defaultdict(collections.Counter)
for t in threads:
    S, ft, fu, stt, rt = t["stringArray"], t["frameTable"], t["funcTable"], t["stackTable"], t.get("resourceTable")
    def fr(x):
        f = ft["func"][x]; res = fu["resource"][f]
        lib = libs[rt["lib"][res]]["debugName"] if rt is not None and res is not None and res >= 0 else "?"
        n = S[fu["name"][f]]
        if "execution" in lib.lower():
            a = ft["address"][x] if "address" in ft and ft["address"][x] is not None and ft["address"][x] >= 0 else None
            m = re.match(r"^(?:fun_|0x)([0-9a-f]+)$", n)
            rva = a if a is not None else (int(m.group(1), 16) if m else None)
            return ("exe", name(rva) if rva is not None else n)
        return (lib, n)
    for s in t["samples"]["stack"]:
        if s is None: continue
        ch = []
        while s is not None: ch.append(fr(stt["frame"][s])); s = stt["prefix"][s]
        if ch[0][1].startswith(IDLE): continue
        root = "truncated" if len(ch) >= 256 else ("thread" if ch[-1][1] == "0xc9c5b" else f"root {ch[-1][0]}!{ch[-1][1]}")
        names = " ".join(n for _, n in ch)
        g[root]["all"] += 1
        for k, v in KEYS.items():
            if v in names: g[root][k] += 1
for r, c in g.items():
    print(r, dict(c))
