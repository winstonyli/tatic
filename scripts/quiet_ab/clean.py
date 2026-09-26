# Classify each logged run as clean or dirty from the sampler log.
# A sample stamped t covers (t-2, t]; run stamps are whole seconds, so a
# run uses every sample with start <= t <= end + 2 (its interval overlaps),
# and a run shorter than one interval still gets one or two. The load from
# other processes is the mean total over those samples minus the run's own
# CPU time (its cpu= field) spread over the time they cover. Dirty if the
# run failed (rc != 0), a selfplay/League process existed in any sample, or
# other processes averaged 20% of the machine or more.
# Old logs (4-column samples with an own-% column, no cpu= field) use
# total minus own per sample.
import os, sys
# AB_CORES pins the core count for test_clean.sh.
CORES, DT = int(os.environ.get('AB_CORES', os.cpu_count())), 2
def parse(l):
    f = l.split()
    if len(f) == 3: return float(f[0]), float(f[1]), None, int(f[2])
    if len(f) == 4: return float(f[0]), float(f[1]), float(f[2]), int(f[3])
samples = [x for x in map(parse, open(sys.argv[1])) if x]
runs = [l.split() for l in open(sys.argv[2]) if l.startswith('run ')]
for _, label, rnd, s, e, *rest in runs:
    s, e = float(s), float(e)
    kv = dict(x.split('=', 1) for x in rest)
    if kv.get('rc', '0') != '0':
        print(label, rnd, 'dirty', 'rc=' + kv['rc']); continue
    w = [x for x in samples if s <= x[0] <= e + DT]
    if not w:
        print(label, rnd, 'dirty', 'nosamples'); continue
    total = sum(x[1] for x in w) / len(w)
    if kv.get('cpu', '?') != '?':
        own = 100 * float(kv['cpu']) / (CORES * DT * len(w))
    elif w[0][2] is not None:
        own = sum(x[2] for x in w) / len(w)
    else:
        print(label, rnd, 'dirty', 'noown'); continue
    foreign = max(0, total - own)
    sp = max(x[3] for x in w)
    ok = sp == 0 and foreign < 20
    print(label, rnd, 'clean' if ok else 'dirty', f'foreign={foreign:.0f}% selfplay={sp} n={len(w)}')
