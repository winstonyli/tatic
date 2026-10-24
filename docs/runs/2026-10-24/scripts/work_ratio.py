"""Work counts' proxy quality (plan docs/superpowers/plans/2026-10-23-work-counts.md, Task 4 Step 3).

work_ratio.py <A/A run dir>... -- <ablation run dir>...: reads each run's out.log salt lines (scripts/streams_ab.sh) and
prints, per counter, the A/A spread (max over salts of |A - B| / mean), the spread of job CPU / counter over every
arm-salt (max / min - 1), and for the ablation runs, summed over their salts, how B moved against A in each counter,
their sum and job CPU.
"""
import re
import sys
from pathlib import Path

LINE = re.compile(r"^salt (\d+): M A (\d+) B (\d+); held A (\S+) B (\S+); jobcpu A ([0-9.]+) B ([0-9.]+); work A (.*) B (.*)$")


def work(s):
    return {k: int(v) for k, v in (kv.split("=") for kv in s.split())}


def salts(dirs):
    out = []
    for d in dirs:
        for line in (Path(d) / "out.log").read_text(encoding="utf-8", errors="replace").splitlines():
            m = LINE.match(line.strip())
            if m:
                out.append({"run": Path(d).name, "salt": int(m[1]), "M": (int(m[2]), int(m[3])), "held": (m[4], m[5]),
                            "cpu": (float(m[6]), float(m[7])), "work": (work(m[8]), work(m[9]))})
    return out


def main(argv):
    cut = argv.index("--")
    aa, ab = salts(argv[:cut]), salts(argv[cut + 1:])
    counters = list(aa[0]["work"][0])
    print(f"A/A salts {sorted(s['salt'] for s in aa)}; ablation salts {sorted(s['salt'] for s in ab)}")
    for k in counters:
        spread = max(abs(s["work"][0][k] - s["work"][1][k]) / ((s["work"][0][k] + s["work"][1][k]) / 2) for s in aa)
        ratios = [s["cpu"][i] / s["work"][i][k] for s in aa + ab for i in (0, 1)]
        print(f"{k}: A/A spread {spread * 1e6:.2f} ppm; cpu/count over {len(ratios)} arm-salts max/min-1 {max(ratios) / min(ratios) - 1:.1%}")
    cpu = max(abs(s["cpu"][0] - s["cpu"][1]) / ((s["cpu"][0] + s["cpu"][1]) / 2) for s in aa)
    print(f"job cpu: A/A spread {cpu:.1%}")
    if ab:
        tot = lambda i, k: sum(s["work"][i][k] for s in ab)
        moves = {k: tot(1, k) / tot(0, k) - 1 for k in counters}
        moves["sum"] = sum(tot(1, k) for k in counters) / sum(tot(0, k) for k in counters) - 1
        moves["job cpu"] = sum(s["cpu"][1] for s in ab) / sum(s["cpu"][0] for s in ab) - 1
        print("ablation B against A, summed: " + ", ".join(f"{k} {v:+.2%}" for k, v in moves.items()))
        print("M A/B per salt: " + ", ".join(f"{s['salt']}: {s['M'][0]}/{s['M'][1]} held {s['held'][0]}/{s['held'][1]}" for s in sorted(ab, key=lambda s: s["salt"])))


if __name__ == "__main__":
    main(sys.argv[1:])
