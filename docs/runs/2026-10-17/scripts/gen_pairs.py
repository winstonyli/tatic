# gen_pairs.py [--best <arm>] <run dir>...: per arm (<arm>_<salt>/cold.tsv in any of the run dirs), mined-batch M per
# family (column 5's 2nd and 3rd entries), rules and loop seconds (columns 6 and 7) summed over its salts, then its paired
# count against the best arm over the salts both have: better, equal, worse. The best is --best, else the generator arm
# (f04 f08 s08 s16 m08; controls never) with the lowest total among those with the most salts, so totals compare like with
# like. The law generator's plan, Task 7.
import sys, os, re, collections
args = sys.argv[1:]
forced = args[1] if args[:1] == ["--best"] else None
dirs = args[2:] if forced else args
rows = collections.defaultdict(dict)  # arm -> salt -> (M per family, rules, secs)
for d in dirs:
    for e in os.listdir(d):
        m = re.fullmatch(r"(.+)_(\d+)", e)
        p = os.path.join(d, e, "cold.tsv")
        if not m or not os.path.isfile(p): continue
        fam, rules, secs = collections.Counter(), 0, 0
        for line in open(p):
            c = line.rstrip("\n").split("\t")
            ms = [int(x) for x in c[4].split(",")]
            fam[c[0]] += ms[1] + ms[2]; rules += int(c[5]); secs += int(c[6])
        rows[m.group(1)][int(m.group(2))] = (fam, rules, secs)
tot = {a: sum(sum(f.values()) for f, _, _ in s.values()) for a, s in rows.items()}
gens = [a for a in rows if a in ("f04", "f08", "s08", "s16", "m08")]
most = max((len(rows[a]) for a in gens), default=0)
best = forced or min((a for a in gens if len(rows[a]) == most), key=lambda a: (tot[a], a))
print(f"best: {best} ({len(rows[best])} salts)")
for a in sorted(rows, key=lambda a: (-len(rows[a]), tot[a], a)):
    s = rows[a]
    fam = collections.Counter()
    for f, _, _ in s.values(): fam.update(f)
    common = sorted(set(s) & set(rows[best]))
    mt = lambda arm, k: sum(rows[arm][k][0].values())
    b = sum(mt(a, k) < mt(best, k) for k in common); w = sum(mt(a, k) > mt(best, k) for k in common)
    print(f"{a}: salts {len(s)} M {tot[a]} (cmp3d {fam['cmp3d']} add3 {fam['add3']} sbo3 {fam['sbo3']}) rules {sum(r for _, r, _ in s.values())} "
          f"loop secs {sum(x for _, _, x in s.values())} vs {best}: better {b} equal {len(common) - b - w} worse {w}")
