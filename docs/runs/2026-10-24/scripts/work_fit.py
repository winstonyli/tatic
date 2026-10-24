"""Job CPU as a weighted sum of the work counts, fitted by least squares (spec decision 6(b), the fitted weights).

work_fit.py <run dir>...: every arm-salt of the runs' out.log salt lines (work_ratio.py's parser); prints the weights in
ns per count, and the spread (max / min - 1) of job CPU / fit, against the best single counter's job CPU / count.
"""
import sys

from work_ratio import salts


def solve(a, b):
    n = len(b)
    m = [row[:] + [v] for row, v in zip(a, b)]
    for c in range(n):
        p = max(range(c, n), key=lambda r: abs(m[r][c]))
        m[c], m[p] = m[p], m[c]
        for r in range(n):
            if r != c:
                f = m[r][c] / m[c][c]
                m[r] = [x - f * y for x, y in zip(m[r], m[c])]
    return [m[i][n] / m[i][i] for i in range(n)]


def main(dirs):
    rows = [(s["work"][i], s["cpu"][i]) for s in salts(dirs) for i in (0, 1)]
    ks = list(rows[0][0])
    x = [[w[k] / 1e9 for k in ks] for w, _ in rows]
    y = [c for _, c in rows]
    ata = [[sum(r[i] * r[j] for r in x) for j in range(len(ks))] for i in range(len(ks))]
    aty = [sum(r[i] * v for r, v in zip(x, y)) for i in range(len(ks))]
    w = solve(ata, aty)
    fit = [sum(a * b for a, b in zip(r, w)) for r in x]
    q = [v / f for v, f in zip(y, fit)]
    print(f"{len(rows)} arm-salts; weights (ns per count): " + ", ".join(f"{k} {v:.2f}" for k, v in zip(ks, w)))
    print(f"job cpu / fit: max/min-1 {max(q) / min(q) - 1:.1%}")


if __name__ == "__main__":
    main(sys.argv[1:])
