"""rule_ablation_stats.py <out.log>: summarize rule_ablation.sh's rows. Per family: Spearman rank correlations between the
miner's logged in-sample gain, the leave-one-out drop in free laws on the mine laws (in), and the drop on held-out
laws (h = size 9 + size 11); how many rules matter (drop > 0) in-sample, held out, both; and the summed drops."""
import sys


def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i])
    r = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i
        while j + 1 < len(order) and xs[order[j + 1]] == xs[order[i]]:
            j += 1
        for k in range(i, j + 1):
            r[order[k]] = (i + j) / 2
        i = j + 1
    return r


def spearman(a, b):
    ra, rb = ranks(a), ranks(b)
    n = len(a)
    ma, mb = sum(ra) / n, sum(rb) / n
    cov = sum((x - ma) * (y - mb) for x, y in zip(ra, rb))
    va = sum((x - ma) ** 2 for x in ra) ** 0.5
    vb = sum((y - mb) ** 2 for y in rb) ** 0.5
    return cov / (va * vb) if va and vb else float("nan")


fams = {}
for line in open(sys.argv[1]):
    if line.startswith("#") or not line.strip():
        continue
    f, i, g, inf, _, h9, _, h11, _ = line.split()
    fams.setdefault(f, []).append((int(i), g, int(inf), int(h9), int(h11)))

for f, rows in fams.items():
    base = next(r for r in rows if r[0] == 0)
    rs = [r for r in rows if r[0] != 0]
    gain = [int(r[1]) for r in rs]
    d_in = [base[2] - r[2] for r in rs]
    d_h = [(base[3] + base[4]) - (r[3] + r[4]) for r in rs]
    both = sum(1 for a, b in zip(d_in, d_h) if a > 0 and b > 0)
    only_in = sum(1 for a, b in zip(d_in, d_h) if a > 0 and b <= 0)
    only_h = sum(1 for a, b in zip(d_in, d_h) if a <= 0 and b > 0)
    neg_h = sum(1 for b in d_h if b < 0)
    print(f"{f}: {len(rs)} rules; full library free in {base[2]}, h9 {base[3]}, h11 {base[4]}")
    print(f"  spearman gain~in {spearman(gain, d_in):.2f}  gain~held {spearman(gain, d_h):.2f}  in~held {spearman(d_in, d_h):.2f}")
    print(f"  drop > 0: in {sum(1 for a in d_in if a > 0)}, held {sum(1 for b in d_h if b > 0)}; both {both}, in only {only_in}, held only {only_h}; held drop < 0 (removal helps) {neg_h}")
    print(f"  summed drop: in {sum(d_in)}, held {sum(d_h)}; summed gain {sum(gain)}")
    top = sorted(zip(gain, d_in, d_h, [r[0] for r in rs]), key=lambda t: -t[0])[:5]
    print("  top 5 by gain (gain, in drop, held drop, idx): " + "; ".join(f"{g} {a} {b} #{i}" for g, a, b, i in top))
    toph = sorted(zip(gain, d_in, d_h, [r[0] for r in rs]), key=lambda t: -t[2])[:5]
    print("  top 5 by held drop (gain, in drop, held drop, idx): " + "; ".join(f"{g} {a} {b} #{i}" for g, a, b, i in toph))
