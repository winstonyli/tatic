# The figures quoted from run 2026-10-28-stream-probe (docs/tier-cycle.md, "Grouping the streams' terms"), derived from
# the raw folder's probe.log, probe2.log (the patch's PROBE rows, one per stream and growth count) and check.log
# (`stream_probe_overhead`'s CHECK rows). Usage: python -P stream_probe_derive.py <raw folder> < /dev/null
import re, statistics, sys

base = sys.argv[1]


def rows(fname, tag):
    out = {}
    for line in open(f"{base}/{fname}", encoding="utf-8", errors="replace"):
        m = re.match(rf"{tag} L=(\d+) (\S+) (.*)", line.strip())
        if m:
            out[(int(m.group(1)), m.group(2))] = {k: float(v) for k, v in (kv.split("=") for kv in m.group(3).split())}
    return out


runs = {"run 1": rows("probe.log", "PROBE"), "run 2": rows("probe2.log", "PROBE")}
for run, r in runs.items():
    for L in (2, 4):
        s = {n: d for (l, n), d in r.items() if l == L}
        tot = lambda k: sum(d[k] for d in s.values())
        pipe = tot("t_pipe")
        pc = sum(tot(k) for k in ("t_fill", "t_key", "t_ins", "t_conj"))
        ol = sum(tot(k) for k in ("t_post", "t_osetup", "t_shuf", "t_norm", "t_r8"))
        gr = sum(tot(k) for k in ("t_setup", "t_grow", "t_growth", "t_sort"))
        print(f"== {run}, {L} growths, {len(s)} streams, t_pipe {pipe:.1f} s")
        print(f"  shares: pool_conjectures {100*pc/pipe:.1f} (fill {100*tot('t_fill')/pipe:.1f}, key {100*tot('t_key')/pipe:.1f},"
              f" insert {100*tot('t_ins')/pipe:.1f}, conjecture sort {100*tot('t_conj')/pipe:.1f}), open-law filter {100*ol/pipe:.1f}"
              f" (normalize {100*tot('t_norm')/pipe:.1f}, width 8 {100*tot('t_r8')/pipe:.1f}), growth+sort+setup {100*gr/pipe:.1f}")
        print(f"  terms in groups of two or more: {100*tot('in_multi')/tot('pool'):.1f}% of {tot('pool'):.0f}")
        single = tot("t_fill") + tot("t_key") + tot("t_ins")
        for k in (16, 64, 256):
            two = tot(f"t_pre{k}a") + tot(f"t_pre{k}b")
            print(f"  {k} inputs: terms kept {100*tot(f'pre{k}_terms')/tot('pool'):.2f}% (floor {100*tot('in_multi')/tot('pool'):.2f}),"
                  f" fills kept {100*tot(f'pre{k}_filled')/tot('filled'):.2f}%; fill+key+insert {single:.1f} s -> {two:.1f} s")
            pairs = [(d[f"t_pre{k}a"] + d[f"t_pre{k}b"], d["t_fill"] + d["t_key"] + d["t_ins"]) for d in s.values()]
            for label, least in (("streams whose single stage takes 0.05 s or more", 0.05), ("all streams", 0.0)):
                kept = [(two, one) for two, one in pairs if one >= least]
                ratios = [two / one for two, one in kept if one > 0]
                print(f"    {label} ({len(kept)}): median two-stage/single {statistics.median(ratios):.3f},"
                      f" slower on {sum(two > one for two, one in kept)}")
        hi = sorted(n for n, d in s.items() if d["pre16_terms"] > 0.9 * d["pool"])
        print(f"  streams keeping over 90% of their terms at 16 inputs: {len(hi)}")
        if "add,sub" in s:
            d = s["add,sub"]
            print(f"  add,sub: pool {d['pool']:.0f}, in groups of two or more {d['in_multi']:.0f} in {d['multi']:.0f} groups"
                  f" ({d['groups']:.0f} groups in all), kept at 16 inputs {d['pre16_terms']:.0f}")
        empty = sorted(n for n, d in s.items() if d["out"] == 0)
        print(f"  streams with no laws: {empty}")

chk = rows("check.log", "CHECK")
main = runs["run 1"]
for L in (2, 4):
    t = chk[(L, "TOTAL")]
    print(f"== check.log {L} growths TOTAL: " + " ".join(f"{k}={v:.2f}" for k, v in t.items()))
    keys = [k for k in chk if k[0] == L and k[1] != "TOTAL"]
    for run, r in runs.items():
        print(f"  the {len(keys)} checked streams in {run}: normalize {sum(r[k]['t_norm'] for k in keys):.2f} s,"
              f" probe {sum(r[k]['t_pipe'] for k in keys):.2f} s")
