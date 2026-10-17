# gate_cmp.py <run dir> <tag>: compare <run dir>/<tag>_old_<s> with <tag>_new_<s> for salts 1 and 2, with timings and libtest's
# harness lines normalized away; a difference that sorting both files removes is reported as "(order only)". One process: the
# shell version started a few processes per file at about 0.2 s each in Git Bash, 14 minutes a gate (docs/tier-cycle.md,
# "Survey: a lemma library kept across sweeps"). Run it as `python -P gate_cmp.py <run dir> <tag> < /dev/null`.
import os, re, sys

TIME = re.compile(rb"[0-9]+(\.[0-9]+)?(s|ms|\xc2\xb5s)\b")
DROP = re.compile(rb"^(running [0-9]+ tests?|test .* \.\.\. (ok|FAILED|ignored)|test result: .*|)$")
CUT = {"cold.tsv": 7, "own.tsv": 7, "pooled.tsv": 7, "mines.tsv": 2, "pooled_prefs.tsv": 2, "m.tsv": 5}  # the 1-based field dropped


def norm(path, tag):
    data = open(path, "rb").read()
    name = os.path.basename(path)
    lines = data.split(b"\n")
    if lines and lines[-1] == b"":
        lines.pop()
    if name in CUT:
        f = CUT[name] - 1
        # as `cut`: a line with no tab is kept whole
        return [l if b"\t" not in l else b"\t".join(p for i, p in enumerate(l.split(b"\t")) if i != f) for l in lines]
    if name.endswith((".txt", ".log")):
        run = re.compile(re.escape(tag.encode()) + rb"_(old|new)")
        out = []
        for l in lines:
            l = TIME.sub(b"T", l)
            l = run.sub(b"RUN", l)
            l = re.sub(rb"[0-9]+ filtered out", b"N filtered out", l, count=1)
            if not DROP.match(l):
                out.append(l)
        return out
    return lines


def files(d):
    return sorted("./" + os.path.relpath(os.path.join(r, f), d).replace(os.sep, "/") for r, _, fs in os.walk(d) for f in fs)


def main():
    sys.stdout.reconfigure(newline="\n")  # LF, so shell callers can compare the output
    k, tag = sys.argv[1], sys.argv[2]
    for s in (1, 2):
        o, n = os.path.join(k, f"{tag}_old_{s}"), os.path.join(k, f"{tag}_new_{s}")
        try:
            lo, ln = files(o), files(n)
        except OSError as e:
            print(f"ERROR salt {s}: listing failed ({e})")
            continue
        if lo == ln:
            print(f"salt {s}: same file list ({len(lo)} files)")
        else:
            for f in sorted(set(lo) - set(ln)):
                print(f"< {f}")
            for f in sorted(set(ln) - set(lo)):
                print(f"> {f}")
        for f in lo:
            try:
                a, b = norm(os.path.join(o, f), tag), norm(os.path.join(n, f), tag)
            except OSError as e:
                print(f"ERROR salt {s}: normalizing {f} failed ({e})")
                continue
            if a == b:
                continue
            print(f"DIFF salt {s} {f} (order only)" if sorted(a) == sorted(b) else f"DIFF salt {s} {f}")
    print("cmp done")


main()
