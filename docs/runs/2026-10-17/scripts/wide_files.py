# wide_files.py <out root> <src arm>=<run root>/<prefix>...: per salt, family and phase of each source arm, write extras files
# for gen_twin.sh from laws_extra_0.txt, using twin_wide.py's class normalization (both sides, served laws of phases 1-3):
#   <prefix>_full     every extra (a replay);
#   <prefix>_class    the extras that are no class twin of a served law;
# and for the pad source also
#   pad_notriv        pad_class without the laws whose sides normalize to the same term;
#   pad_ctl           pad_class without as many of its other laws, chosen by a fixed hash.
import sys, os, hashlib
here = os.path.dirname(os.path.abspath(__file__))
argv = sys.argv
sys.argv = [argv[0], "", ""]
exec(open(os.path.join(here, "twin_wide.py")).read().split("root, prefixes = ")[0])

out = argv[1]
def write(arm, salt, fam, p, lines):
    od = os.path.join(out, arm, f"s{salt}")
    os.makedirs(od, exist_ok=True)
    open(os.path.join(od, f"{fam}_{p}.txt"), "w", newline="\n").write("".join(l + "\n" for l in lines))

for spec in argv[2:]:
    root = os.path.dirname(spec); pre = os.path.basename(spec)
    for arm in sorted(os.listdir(root)):
        if not (arm.startswith(pre + "_") and arm[len(pre) + 1:].isdigit()): continue
        salt = arm[len(pre) + 1:]
        d = os.path.join(root, arm)
        for fam in ["cmp3d", "add3", "sbo3"]:
            loops = [os.path.join(d, f"cold_{fam}_{p}_none") for p in (1, 2, 3)]
            served = {nkey(a, b, norm_class) for lp in loops
                      for f in ("laws_serve_0.txt", "laws_serve_100.txt", "laws_serve_200.txt")
                      for a, b in laws(os.path.join(lp, f))}
            for p, lp in zip((1, 2, 3), loops):
                lines = [l.rstrip("\n") for l in open(os.path.join(lp, "laws_extra_0.txt")) if " = " in l]
                ks = [nkey(*l.split(" = ", 1), norm_class) for l in lines]
                keep = [l for l, k in zip(lines, ks) if k is None or k not in served]
                write(f"{pre}_full", salt, fam, p, lines)
                write(f"{pre}_class", salt, fam, p, keep)
                if pre == "pad":
                    triv = {l for l, k in zip(lines, ks) if k is None}
                    others = sorted((l for l in keep if l not in triv), key=lambda l: hashlib.sha1(l.encode()).hexdigest())
                    drop = set(others[:len(triv)])
                    write("pad_notriv", salt, fam, p, [l for l in keep if l not in triv])
                    write("pad_ctl", salt, fam, p, [l for l in keep if l not in drop])
                print(pre, salt, fam, p, len(lines), len(keep), sum(k is None for k in ks))
