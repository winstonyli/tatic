# order_fx.py <runs.tsv>...: per quiet_ab.sh A/B, the second arm's mean extra job CPU, and the later-named arm minus the
# earlier averaged over the two orders (each arm first in half the rounds). Run as python -P order_fx.py ... < /dev/null.
import sys, csv, statistics as st
for path in sys.argv[1:]:
    rows = [r for r in csv.DictReader(open(path), delimiter='\t') if r['clean'] == 'true']
    rounds = {}
    for r in rows: rounds.setdefault(r['round'], {})[int(r['position'])] = (r['arm'], float(r['jobcpu_s']))
    arms = sorted({r['arm'] for r in rows}); a, b = arms[0], arms[-1]
    pos, eff = [], {True: [], False: []}
    for rd in rounds.values():
        if 1 not in rd or 2 not in rd: continue
        pos.append(rd[2][1] - rd[1][1])
        d = {rd[1][0]: rd[1][1], rd[2][0]: rd[2][1]}
        eff[rd[1][0] == b].append(d[b] - d[a])
    e = (st.mean(eff[True]) + st.mean(eff[False])) / 2 if eff[True] and eff[False] else float('nan')
    print(f"{path.split('/')[-1]}: pos2-pos1 mean {st.mean(pos):+.1f} s (n={len(pos)}, {sum(p>0 for p in pos)} pos2 slower); {b}-{a} balanced {e:+.1f} s; {b} first {[round(x,1) for x in eff[True]]}, second {[round(x,1) for x in eff[False]]}")
