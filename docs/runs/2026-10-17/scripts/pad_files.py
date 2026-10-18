# pad_files.py <pad run root> <out root>: per pad_<salt>, family and phase, write two extras files from laws_extra_0.txt:
# untwin/s<salt>/<fam>_<p>.txt drops the laws whose stripped form is a twin of a served law of phases 1-3;
# control/s<salt>/<fam>_<p>.txt drops as many of the other laws, chosen by a fixed hash.
import sys, os, hashlib
sys.argv = [sys.argv[0], sys.argv[1]] + sys.argv[2:]
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, "pad_strip.py")).read().split("root = sys.argv[1]")[0]
exec(src)

root, out = sys.argv[1], sys.argv[2]
for arm in sorted(os.listdir(root)):
    if not arm.startswith("pad_"): continue
    salt = arm[4:]
    d = os.path.join(root, arm)
    for fam in ["cmp3d", "add3", "sbo3"]:
        loops = [os.path.join(d, f"cold_{fam}_{p}_none") for p in (1, 2, 3)]
        served = set()
        for lp in loops:
            for f in ["laws_serve_0.txt", "laws_serve_100.txt", "laws_serve_200.txt"]:
                served.update(key(a, b) for a, b in laws(os.path.join(lp, f)))
        for p, lp in zip((1, 2, 3), loops):
            lines = [l.rstrip("\n") for l in open(os.path.join(lp, "laws_extra_0.txt")) if " = " in l]
            twin = []
            for l in lines:
                a, b = l.split(" = ", 1)
                sa, sb = show(strip(parse(a))), show(strip(parse(b)))
                twin.append(sa != sb and key(sa, sb) in served)
            keep_u = [l for l, t in zip(lines, twin) if not t]
            others = [l for l, t in zip(lines, twin) if not t]
            drop = set(sorted(others, key=lambda l: hashlib.sha1(l.encode()).hexdigest())[: sum(twin)])
            keep_c = [l for l in lines if l not in drop]
            for name, keep in (("untwin", keep_u), ("control", keep_c)):
                od = os.path.join(out, name, f"s{salt}")
                os.makedirs(od, exist_ok=True)
                open(os.path.join(od, f"{fam}_{p}.txt"), "w", newline="\n").write("".join(l + "\n" for l in keep))
            print(salt, fam, p, len(lines), sum(twin))
