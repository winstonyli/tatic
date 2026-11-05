import itertools, collections, sys
# Terms over x, y with add, sub, and, or, xor, shl1, shr1, at word widths 3..6 (mod 2^n).
# A law = two distinct terms equal at all widths 3..6 and all inputs. Report how many laws involve shr1 under add/sub
# (the case the machine model cannot take) versus shr1 only under bitwise ops / shifts (already covered by STerm).
W = [3, 4, 5, 6]
pts = {w: [(a, b) for a in range(1 << w) for b in range(1 << w)] for w in W}
def ev(t, w, a, b):
    m = (1 << w) - 1
    if t == 'x': return a
    if t == 'y': return b
    op = t[0]
    if op in ('shl', 'shr'):
        v = ev(t[1], w, a, b)
        return (v << 1) & m if op == 'shl' else v >> 1
    l, r = ev(t[1], w, a, b), ev(t[2], w, a, b)
    return {'add': (l + r) & m, 'sub': (l - r) & m, 'and': l & r, 'or': l | r, 'xor': l ^ r}[op]
def fp(t):
    return tuple(ev(t, w, a, b) for w in W for (a, b) in pts[w][::7 if w > 4 else 1])
def shr_in_arith(t, under=False):
    if isinstance(t, str): return False
    u = under
    # shr1 whose operand contains add/sub, or add/sub whose operand contains shr1
    if t[0] == 'shr' and has(t[1], ('add', 'sub')): return True
    return any(shr_in_arith(c, u) for c in t[1:])
def has(t, ops):
    return not isinstance(t, str) and (t[0] in ops or any(has(c, ops) for c in t[1:]))
def uses(t, op):
    return not isinstance(t, str) and (t[0] == op or any(uses(c, op) for c in t[1:]))
by_size = {1: ['x', 'y']}
N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
for s in range(2, N + 1):
    out = []
    for t in by_size[s - 1]:
        out += [('shl', t), ('shr', t)]
    for i in range(1, s - 1):
        j = s - 1 - i
        for l in by_size[i]:
            for r in by_size[j]:
                for op in ('add', 'sub', 'and', 'or', 'xor'):
                    out.append((op, l, r))
    by_size[s] = out
classes = collections.defaultdict(set)
for s in by_size:
    for t in by_size[s]:
        classes[fp(t)].add(t)
laws = [c for c in classes.values() if len(c) > 1]
with_shr = [c for c in laws if any(uses(t, 'shr') for t in c)]
hard = [c for c in with_shr if any(shr_in_arith(t) for t in c)]
# classes that mix a shr-free term with a shr term: a law only provable with shr
mixed = [c for c in with_shr if any(not uses(t, 'shr') for t in c)]
# shr-free class partner exists in some term of the class under an arithmetic shr
print('terms', sum(len(v) for v in by_size.values()), 'classes', len(classes), 'laws(classes>1)', len(laws))
print('classes with shr', len(with_shr), 'with shr under/over add-sub', len(hard), 'mixing shr and shr-free terms', len(mixed))
def show(t):
    return t if isinstance(t,str) else '(%s %s)'%(t[0],' '.join(show(c) for c in t[1:]))
for c in sorted(hard, key=lambda c: min(len(show(t)) for t in c))[:14]:
    print(' ~ '.join(sorted((show(t) for t in c), key=len)[:3]))

def arith(t): return has(t, ('add','sub'))
pure = [c for c in hard if any(not arith(t) for t in c)]
print('hard classes', len(hard), 'with a member free of add/sub (bitwise+shifts only):', len(pure))
# of those, classes whose hard terms can be reduced by shl rewriting alone: hard member only because of shr over (add x x)/(shl) style
def only_double(t):
    # shr operand arithmetic consisting solely of (add p p) nodes
    if isinstance(t,str): return True
    if t[0]=='shr' and has(t[1],('add','sub')):
        def ok(u):
            if isinstance(u,str): return True
            if u[0] in ('add',): return u[1]==u[2] and ok(u[1])
            if u[0]=='sub': return False
            return all(ok(c) for c in u[1:])
        return ok(t[1])
    return all(only_double(c) for c in t[1:])
dbl = [c for c in pure if all(only_double(t) for t in c if shr_in_arith(t))]
print('of those, hard members only through add p p (reducible by the double rule):', len(dbl))
rest = [c for c in hard if c not in pure]
print('no pure member:', len(rest))
for c in rest[:6]: print('  ', ' ~ '.join(sorted((show(t) for t in c), key=len)[:3]))
