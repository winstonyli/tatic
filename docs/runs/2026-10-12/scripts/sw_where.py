import collections, gzip, json, re, subprocess, sys

# sw_where.py <dir> [regex]: where a samply profile of a sweep (<dir>/sw.json.gz, recorded with samply `profile.ps1`)
# spends its CPU. Only sw.exe threads count; each sample is weighted by its threadCPUDelta (the CPU it used: samples
# that ran nothing weigh 0), and wait leaves are dropped. Exe frames (fun_<rva>) are named with llvm-symbolizer against
# <dir>/sw.exe and its PDB. Prints named inclusive buckets, leaf libraries, top self and inclusive functions, the top
# leaves with their callers, and with [regex] the inclusive share of each matching function, what runs under it, and
# the nearest tatic or church_bv caller of the innermost match that does not itself match.
# Writes <dir>/counts.json for sw_diff.py. docs/tier-cycle.md, "Samples are not CPU".
D = sys.argv[1]
p = json.load(gzip.open(f"{D}/sw.json.gz"))
syms = json.load(open(f"{D}/sw.json.syms.json"))
ST = syms["string_table"]
import bisect
tables = {lib["debug_name"]: sorted((e["rva"], e["size"], ST[e["symbol"]]) for e in lib["symbol_table"]) for lib in syms["data"]}
libs = p["libs"]
# waits: the driver's blocking read of the worker's pipe is NtReadFile
IDLE = ("NtWaitFor", "NtDelayExecution", "NtWaitForWorkViaWorkerFactory", "ZwWaitFor", "NtRemoveIoCompletion", "NtWaitForAlertByThreadId", "NtReadFile", "NtUserMsgWait")
procs = [[t for t in pr["threads"] if t.get("processName") == "sw.exe"] for pr in [p] + p.get("processes", [])]
EXE = re.compile(r"^church_bv")
samples = []
rvas = set()
for threads in procs:
    for t in threads:
        S, ft, fu, stt, rt = t["stringArray"], t["frameTable"], t["funcTable"], t["stackTable"], t.get("resourceTable")
        cache = {}
        def info(fr):
            if fr in cache:
                return cache[fr]
            f = ft["func"][fr]; n = S[fu["name"][f]]; res = fu["resource"][f]
            lib = libs[rt["lib"][res]]["debugName"] if res is not None and res >= 0 else "?"
            m = re.match(r"^(?:fun_|0x)([0-9a-f]+)$", n)
            if m:
                rva = int(m.group(1), 16)
                if EXE.match(lib):
                    n = ("rva", rva); rvas.add(rva)
                else:
                    rows = tables.get(lib); n = f"{lib}:{n}"
                    if rows:
                        i = bisect.bisect_right(rows, (rva, 1 << 62, "")) - 1
                        if i >= 0 and rva < rows[i][0] + max(rows[i][1], 1):
                            n = rows[i][2]
            cache[fr] = (lib, n); return cache[fr]
        for s, w in zip(t["samples"]["stack"], t["samples"].get("threadCPUDelta") or []):
            if s is None:
                continue
            chain = []
            while s is not None:
                chain.append(info(stt["frame"][s])); s = stt["prefix"][s]
            samples.append((chain, w or 0))
rv = sorted(rvas)
open(f"{D}/addrs.txt", "w").write("\n".join(f"0x{0x140000000 + r:x}" for r in rv) + "\n")
with open(f"{D}/addrs.txt") as fin:
    out = subprocess.run(["llvm-symbolizer", f"--obj={D}/sw.exe", "--no-inlines", "--output-style=JSON"], stdin=fin, capture_output=True, text=True).stdout
names = {}
for r, line in zip(rv, out.splitlines()):
    try:
        names[r] = json.loads(line)["Symbol"][0]["FunctionName"] or f"rva_{r:x}"
    except Exception:
        names[r] = f"rva_{r:x}"
def short(s):
    while True:
        s2 = re.sub(r"<[^<>]*>", "", s)
        if s2 == s:
            return s[:110]
        s = s2
BUCKETS = [
    ("kernel (tatic::kernel)", re.compile(r"^tatic::kernel::")),
    ("Spaces::build", re.compile(r"Spaces::build")),
    ("inst_rec", re.compile(r"kernel::inst_rec")),
    ("mimalloc", re.compile(r"^_?mi_|mimalloc")),
    ("hashbrown", re.compile(r"^hashbrown::")),
    ("tatic (any)", re.compile(r"^tatic::")),
    ("church_bv (any)", re.compile(r"^church_bv::")),
    ("Term clone", re.compile(r"^<church_bv::rewrite::Term as core::clone::Clone>::clone")),
    ("Term drop", re.compile(r"^core::ptr::drop_glue::<(alloc::boxed::Box<)?church_bv::rewrite::Term")),
    ("SipHash (std DefaultHasher)", re.compile(r"core::hash::sip::|DefaultHasher|RandomState")),
    ("Term::interp", re.compile(r"^<church_bv::rewrite::Term>::interp")),
    ("rewrite::embeds", re.compile(r"church_bv::rewrite::embeds")),
    ("rewrite_memo", re.compile(r"church_bv::rewrite::rewrite_memo")),
    ("rule_set_kernel_check", re.compile(r"church_bv::search::rule_set_kernel_check")),
    ("tree_encoding", re.compile(r"church_bv::machine::tree_encoding")),
    ("lemma_cache (any)", re.compile(r"church_bv::lemma_cache::")),
    ("lemma_cache::Cache::load", re.compile(r"lemma_cache::Cache>::load|lemma_cache::parse")),
    ("lemma_cache::lookup", re.compile(r"lemma_cache::lookup")),
    ("lemma_cache::record", re.compile(r"lemma_cache::record")),
    ("lemma_cache::Save drop", re.compile(r"lemma_cache::Save")),
    ("exe_identity", re.compile(r"lemma_cache::exe_identity")),
    ("task:: (PerTask)", re.compile(r"church_bv::task::")),
    ("SRW lock", re.compile(r"SRWLock|RtlAcquireSRW|futex|WaitOnAddress")),
    ("driver (any)", re.compile(r"church_bv::driver::")),
]
tot = idle = 0
callers = collections.defaultdict(collections.Counter)
bylib = collections.Counter(); selff = collections.Counter(); incl = collections.Counter(); buck = collections.Counter()
for chain, w in samples:
    ch = [(lib, short(names[n[1]]) if isinstance(n, tuple) else short(n)) for lib, n in chain]
    if ch[0][1].startswith(IDLE) or any(c[1].startswith(IDLE) for c in ch if c[0].lower().startswith("ntdll")):
        idle += 1; continue
    tot += w; bylib[ch[0][0]] += w; selff[ch[0][1]] += w
    ns = {c[1] for c in ch}
    full = {names[n[1]] if isinstance(n, tuple) else n for _, n in chain}
    for n in ns:
        incl[n] += w
    for b, rx in BUCKETS:
        if any(rx.search(n) for n in full):
            buck[b] += w
    fl = [names[n[1]] if isinstance(n, tuple) else n for _, n in chain]
    for b in ("SipHash (std DefaultHasher)", "Term clone", "Term drop"):
        rx = dict(BUCKETS)[b]
        i = next((j for j, n in enumerate(fl) if rx.search(n)), None)
        if i is not None:
            c = next((short(n) for n in fl[i + 1:] if re.match(r"^church_bv::", n) and not rx.search(n)), "?")
            callers[b][c] += w
pc = lambda v: f"{100 * v / tot:5.1f}%"
print(f"busy CPU {tot / 1e6:.2f} s (threadCPUDelta in µs) idle-dropped samples {idle} exe rvas {len(rv)} named {sum(1 for v in names.values() if not v.startswith('rva_'))}")
print("== buckets (inclusive)"); [print(f"  {pc(buck[b])} {b}") for b, _ in BUCKETS]
for b, cs in callers.items():
    print(f"== {b}: nearest church_bv caller"); [print(f"  {pc(v)} {n}") for n, v in cs.most_common(6)]
print("== busy by leaf library"); [print(f"  {pc(v)} {n}") for n, v in bylib.most_common(6)]
print("== top self functions"); [print(f"  {pc(v)} {n}") for n, v in selff.most_common(30)]
print("== top inclusive exe functions")
k = 0
for n, v in incl.most_common():
    if re.match(r"^(tatic|church_bv)::", n) and k < 60:
        print(f"  {pc(v)} {n}"); k += 1
print("== top leaves with 4 frames above (lib:name)")
lc = collections.Counter()
for chain, w in samples:
    ch = [(lib, short(names[n[1]]) if isinstance(n, tuple) else short(n)) for lib, n in chain]
    if ch[0][1].startswith(IDLE) or any(c[1].startswith(IDLE) for c in ch if c[0].lower().startswith("ntdll")):
        continue
    lc[" <- ".join(f"{l.split('.')[0]}:{n[:50]}" for l, n in ch[:5])] += w
[print(f"  {pc(v)} {n}") for n, v in lc.most_common(12)]
if len(sys.argv) > 2:
    rx = re.compile(sys.argv[2])
    print(f"== inclusive matching {sys.argv[2]}")
    [print(f"  {pc(v)} {n}") for n, v in [(n, v) for n, v in incl.most_common() if rx.search(n)][:40]]
    # what runs under each matching frame: the next frame below it (callee), by inclusive share
    under = collections.defaultdict(collections.Counter)
    for chain, w in samples:
        ch = [short(names[n[1]]) if isinstance(n, tuple) else short(n) for lib, n in chain]
        if ch[0].startswith(IDLE):
            continue
        for i in range(len(ch) - 1, 0, -1):
            if rx.search(ch[i]):
                under[ch[i]][ch[i - 1]] += w
                break
    for n, cs in under.items():
        print(f"== under {n}"); [print(f"    {pc(v)} {c}") for c, v in cs.most_common(6)]
    # who calls the matching frames: from the innermost match outward, the nearest tatic or church_bv frame that does not match
    near = collections.Counter()
    for chain, w in samples:
        full = [names[n[1]] if isinstance(n, tuple) else n for _, n in chain]
        if short(full[0]).startswith(IDLE):
            continue
        i = next((i for i, n in enumerate(full) if rx.search(short(n))), None)
        if i is not None:
            near[next((short(n) for n in full[i + 1:] if re.match(r"^<?(tatic|church_bv)::", n) and not rx.search(short(n))), "(none)")] += w
    print("== nearest tatic/church_bv caller outside the matches"); [print(f"    {pc(v)} {c}") for c, v in near.most_common(15)]
json.dump({"tot": tot, "self": dict(selff), "incl": dict(incl)}, open(f"{D}/counts.json", "w"))
