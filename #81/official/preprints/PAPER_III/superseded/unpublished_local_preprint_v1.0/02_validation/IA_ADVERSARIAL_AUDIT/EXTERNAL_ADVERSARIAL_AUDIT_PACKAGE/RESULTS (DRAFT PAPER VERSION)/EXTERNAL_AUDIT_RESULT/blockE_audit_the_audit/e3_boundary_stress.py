r"""
EXTERNAL ADVERSARIAL AUDIT — Block E, task E3: stress the internal audit's blind spots.

1. Their shared module `common/audit_formulas.py` is the single point of failure for
   blocks 02-04 (F, mu, Ca, T, r_p all come from it). We diff THEIR implementation
   against OUR independently written closed forms on boundary + random instances:
   d=0, d=p, q=0, q=2p, q=2p+1, p=2304, p huge, plus 20,000 random (p,q,d).
   A transcription error in their module would corrupt all their grids at once.

2. Their grids stop early (block02: q<=8 even when 2p=16; block03: p<=48;
   block04: p<=5, q<=6). The extended coverage lives in this deliverable's Block C
   (C1: p<=40 full + p<=10^4 certified; C2: p<=150 full + p<=10^9 random;
   C3: p<=7 with adversarial profiles + exact nu3 sample); this script re-asserts
   the specific boundary families their grids missed, using OUR formulas only.

Output: results/e3_boundary_results.txt
"""
import sys, os, random
from fractions import Fraction as Q

random.seed(7)
HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.normpath(os.path.join(HERE, '..', '..',
      'EXTERNAL_ADVERSARIAL_AUDIT_PACKAGE', 'OUR_INTERNAL_AUDIT', 'common'))
sys.path.insert(0, PKG)
import audit_formulas as THEIRS  # noqa: E402

OUT = []
def emit(x=''): OUT.append(str(x))

# ---- our independent closed forms (no import from anything of theirs)
def C2(x): return Q(x)*(Q(x)-1)/2
def myF(p, q, d):
    r = p - d
    return min((C2(p) + Q(q)*d)/3, C2(d) + C2(r), C2(d) + (Q(d)*r + C2(r))/3)
def my_mu(a):
    a = Q(a)
    return a*a/12 if a <= Q(2,3) else (2-a)**2/48
def my_Ca(a):
    a = Q(a)
    return (2 - 2*a - a*a)/12
def my_rp(t):
    if t <= 1: return 0
    return t-1 if t % 2 == 0 else t

bad = []
cases = []
for p in [3, 4, 5, 8, 48, 49, 150, 2303, 2304, 2305, 10**6]:
    for q in {0, 1, 8, 2*p - 1, 2*p, 2*p + 1}:
        for d in {0, 1, p//2, p - 1, p}:
            cases.append((p, q, d))
for _ in range(20000):
    p = random.randint(2, 10**6)
    cases.append((p, random.randint(0, 3*p), random.randint(0, p)))
for (p, q, d) in cases:
    tF, _ = THEIRS.F(p, q, d)
    if tF != myF(p, q, d):
        bad.append(('F', p, q, d, str(tF), str(myF(p, q, d))))
emit(f'F cross-check (theirs vs independent): {len(cases)} cases, {len(bad)} mismatches')

bad_mu = []
for num in range(0, 601):
    a = Q(num, 300)
    if THEIRS.mu(a) != my_mu(a) or THEIRS.Ca(a) != my_Ca(a):
        bad_mu.append(str(a))
emit(f'mu/C_alpha cross-check on 601 exact rationals in [0,2]: {len(bad_mu)} mismatches')

bad_rp = [t for t in range(0, 5000) if THEIRS.rp(t) != my_rp(t)]
emit(f'r_p cross-check 0<=t<5000 (incl. boundary conventions chi\'(K_0)=chi\'(K_1)=0): '
     f'{len(bad_rp)} mismatches')

bad_T = []
for _ in range(2000):
    p = random.randint(1, 10**4); q = random.randint(0, 2*p); E = random.randint(0, p*p)
    if THEIRS.T_of_edges(E, p, q) != (Q(E) - (Q(p)+q)**2/6)/2:
        bad_T.append((E, p, q))
emit(f'T(G) cross-check on 2000 random cases: {len(bad_T)} mismatches')

emit()
emit('Grid blind spots of the internal audit (covered by this deliverable):')
emit('  block02 grid q<=8 (never reaches q=2p for p>=5)  -> Block C1: 0<=q<=2p+2 for p<=40,')
emit('     q up to 4p sampled to p=10^4, all EXACT (theirs was float, tol 1e-7).')
emit('  block03 grid p<=48                               -> Block C2: p<=150 exhaustive,')
emit('     200k random to p=10^9, boundary p=2304, all-integer arithmetic.')
emit('  block04 grid p<=5, q<=6, 3 profile families      -> Block C3: p<=7, q<=8, 9 families')
emit('     + 300 random, exact-nu3 refutation sample, CBC status-checked.')
emit()
allbad = bad + bad_mu + bad_rp + bad_T
if allbad:
    emit('MISMATCHES (first 20):')
    for b in allbad[:20]: emit(f'    {b}')
emit('='*72)
emit(f"VERDICT E3: {'PASS — no defect found in the internal audit formulas at any boundary' if not allbad else 'FAIL'}")
emit('='*72)
rep = '\n'.join(OUT)
print(rep)
os.makedirs(os.path.join(HERE, 'results'), exist_ok=True)
with open(os.path.join(HERE, 'results', 'e3_boundary_results.txt'), 'w', encoding='utf-8') as f:
    f.write(rep + '\n')
sys.exit(0 if not allbad else 1)
