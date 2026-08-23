r"""
EXTERNAL ADVERSARIAL AUDIT — Block C, attack on Lemma 4.1 (E-4.1, claim C-5).

    nu3*(G) >= (1/q) * sum_i F(p, q, d_i)     for every split G with q >= 1.

Neither the internal audit nor the paper's own regression suite tests this lemma
computationally (it is only proved by the cloning argument). Here we attack it
directly: nu3*(G) is computed EXACTLY by this audit's own rational tableau simplex
(Bland's rule, fractions.Fraction) on the full triangle LP of the actual graph G
with arbitrary (non-common) neighborhood profiles, and compared against the exact
rational RHS.

Instances: all-profile exhaustive for p=3,4 with q<=3 over distinct sorted profiles
(sampled), plus structured families (staircase, nested, complement, dispersed) and
random profiles for p in 3..6, q in 1..5.  ~200 instances.

Output: results/c7_cloning_results.txt
"""
import sys, os, random, time
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement

random.seed(41)
OUT = []
def emit(x=''): OUT.append(str(x))
def C2i(x): return x*(x-1)//2

def F_exact(p, q, d):
    r = p - d
    return min(Q(C2i(p) + q*d, 3), Q(C2i(d) + C2i(r)),
               Q(C2i(d)) + Q(d*r + C2i(r), 3))

def rational_simplex_max(nvars, rows, rhs, obj):
    mrows = len(rows)
    T = [[Q(0)]*(nvars + mrows + 1) for _ in range(mrows + 1)]
    for i in range(mrows):
        for j, v in rows[i]:
            T[i][j] = Q(v)
        T[i][nvars + i] = Q(1)
        T[i][-1] = Q(rhs[i])
    for j, v in enumerate(obj):
        T[mrows][j] = -Q(v)
    basis = [nvars + i for i in range(mrows)]
    while True:
        ent = next((j for j in range(nvars + mrows) if T[mrows][j] < 0), None)
        if ent is None: break
        leave, bestr = None, None
        for i in range(mrows):
            if T[i][ent] > 0:
                ratio = T[i][-1] / T[i][ent]
                if bestr is None or ratio < bestr or (ratio == bestr and basis[i] < basis[leave]):
                    bestr, leave = ratio, i
        if leave is None: return None
        pv = T[leave][ent]
        T[leave] = [x / pv for x in T[leave]]
        for i in range(mrows + 1):
            if i != leave and T[i][ent] != 0:
                f = T[i][ent]
                T[i] = [x - f*y for x, y in zip(T[i], T[leave])]
        basis[leave] = ent
    return T[mrows][-1]

def nu3_star_exact(p, neigh):
    q = len(neigh)
    tris = [frozenset(t) for t in combinations(range(p), 3)]
    for i, N in enumerate(neigh):
        v = p + i
        for a, b in combinations(sorted(N), 2):
            tris.append(frozenset((a, b, v)))
    edges = [frozenset(e) for e in combinations(range(p), 2)]
    for i, N in enumerate(neigh):
        v = p + i
        for a in N:
            edges.append(frozenset((a, v)))
    if not tris: return Q(0)
    eidx = {e: k for k, e in enumerate(edges)}
    rows = [[] for _ in edges]
    for tj, t in enumerate(tris):
        for e in combinations(sorted(t), 2):
            rows[eidx[frozenset(e)]].append((tj, 1))
    keep = [r for r in rows if r]
    return rational_simplex_max(len(tris), keep, [1]*len(keep), [1]*len(tris))

# instances
inst = []
for p in (3, 4):
    subs = [frozenset(c) for k in range(p + 1) for c in combinations(range(p), k)]
    for q in (1, 2, 3):
        pool = list(combinations_with_replacement(subs, q))
        random.shuffle(pool)
        for prof in pool[:15]:
            inst.append((p, list(prof)))
for p in range(3, 7):
    for q in range(1, 6):
        inst.append((p, [frozenset(range(i % (p + 1))) for i in range(q)]))
        inst.append((p, [frozenset(range(min(p, i + 1))) for i in range(q)]))
        inst.append((p, [frozenset(range(p)) - frozenset({i % p}) for i in range(q)]))
        inst.append((p, [frozenset(x for x in range(p) if random.random() < .6) for _ in range(q)]))
seen = set(); uniq = []
for p, prof in inst:
    key = (p, tuple(sorted(tuple(sorted(N)) for N in prof)))
    if key not in seen:
        seen.add(key); uniq.append((p, prof))

viol = []
tight = 0
t0 = time.time()
for (p, prof) in uniq:
    q = len(prof)
    v = nu3_star_exact(p, prof)
    rhs = sum(F_exact(p, q, len(N)) for N in prof) / q
    if v < rhs:
        viol.append((p, [sorted(N) for N in prof], str(v), str(rhs)))
    if v == rhs: tight += 1
emit(f'Lemma 4.1 exact test: {len(uniq)} distinct-profile split graphs, '
     f'{len(viol)} violations, {tight} tight (equality) instances  [{time.time()-t0:.0f}s]')
if viol:
    emit('VIOLATIONS (first 10):')
    for v_ in viol[:10]: emit(f'    {v_}')
emit('='*72)
emit(f"VERDICT C7 (Lemma 4.1 / E-4.1): {'PASS — no violation; exact rational simplex vs exact RHS' if not viol else 'FAIL'}")
emit('='*72)
rep = '\n'.join(OUT)
print(rep)
here = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(here, 'results'), exist_ok=True)
with open(os.path.join(here, 'results', 'c7_cloning_results.txt'), 'w', encoding='utf-8') as f:
    f.write(rep + '\n')
sys.exit(0 if not viol else 1)
