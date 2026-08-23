r"""
EXTERNAL ADVERSARIAL AUDIT — Block C, attack C2: Theorem 4.2 margin (4.5).

Adversarial exact-integer search for a counterexample to the core inequality

    F(p,q,d) >= q d/2 + (C_alpha + mu(alpha)) p^2 - p/2,    alpha = q/p,

over a grid FAR beyond the internal audit's p<=48, plus random large instances.

Method (independent of the internal audit's Fraction code): multiply the
inequality by 48 so everything is a Python integer (arbitrary precision — no
overflow, no floating point, no Fraction library):

    48*t_k >= 24 q d + 4(2p^2-2pq-q^2) + MU48 - 24 p     for k = 1,2,3
    MU48 = 4 q^2            if 3q <= 2p   (alpha <= 2/3)
         = (2p-q)^2         if 3q >= 2p   (alpha >= 2/3)

    48*t1 = 16*(C(p,2)+q d) ;  48*t2 = 48*(C(d,2)+C(r,2)) ;
    48*t3 = 48*C(d,2) + 16*(d r + C(r,2)),   r = p-d.

We check ALL THREE branches (F >= rhs  <=>  every branch >= rhs), which is the
form actually used in the proof of Theorem 4.2. Any violation is printed as an
explicit counterexample and the script exits nonzero.

Coverage:
  (a) exhaustive 3 <= p <= 150, 1 <= q <= 2p, 0 <= d <= p     (exact integers)
  (b) 200,000 random instances with p up to 10^9              (exact integers)
  (c) boundary sweeps: q = 2p, q = 1, d = 0, d = p, 3q = 2p+-1, p = 2304

Output: results/c2_margin_results.txt
"""
import sys, os, random, time

random.seed(424242)
OUT = []
def emit(x=''): OUT.append(str(x))

def branches48(p, q, d):
    r = p - d
    C2p = p*(p-1)//2
    C2d = d*(d-1)//2
    C2r = r*(r-1)//2
    t1 = 16*(C2p + q*d)
    t2 = 48*(C2d + C2r)
    t3 = 48*C2d + 16*(d*r + C2r)
    return t1, t2, t3

def rhs48(p, q, d):
    mu48 = 4*q*q if 3*q <= 2*p else (2*p - q)*(2*p - q)
    return 24*q*d + 4*(2*p*p - 2*p*q - q*q) + mu48 - 24*p

def check_instance(p, q, d):
    R = rhs48(p, q, d)
    return [k for k, t in enumerate(branches48(p, q, d), 1) if t < R]

violations = []
t0 = time.time()

# (a) exhaustive grid
total_a = 0
for p in range(3, 151):
    for q in range(1, 2*p + 1):
        R_base = 4*(2*p*p - 2*p*q - q*q) + (4*q*q if 3*q <= 2*p else (2*p-q)**2) - 24*p
        C2p = p*(p-1)//2
        for d in range(0, p + 1):
            total_a += 1
            R = 24*q*d + R_base
            r = p - d
            C2d = d*(d-1)//2
            C2r = r*(r-1)//2
            if 16*(C2p + q*d) < R or 48*(C2d + C2r) < R or 48*C2d + 16*(d*r + C2r) < R:
                violations.append(('grid', p, q, d))
emit(f'(a) exhaustive grid 3<=p<=150, 1<=q<=2p, 0<=d<=p: {total_a} instances, '
     f'{len(violations)} violations   [{time.time()-t0:.1f}s]')

# (b) random large instances
t0 = time.time()
total_b = 0
for _ in range(200000):
    p = random.randint(3, 10**9)
    q = random.randint(1, 2*p)
    d = random.randint(0, p)
    total_b += 1
    if check_instance(p, q, d):
        violations.append(('random', p, q, d))
emit(f'(b) random instances p<=10^9: {total_b} instances, '
     f'{sum(1 for v in violations if v[0]=="random")} violations   [{time.time()-t0:.1f}s]')

# (c) boundary sweeps
t0 = time.time()
total_c = 0
bps = list(range(3, 60)) + [149, 150, 1000, 2303, 2304, 2305, 10**6, 10**6+1, 10**9]
for p in bps:
    qs = {1, 2, p//2, (2*p)//3, (2*p)//3 + 1, (2*p+1)//3, 2*p - 1, 2*p}
    ds = {0, 1, p//2, p - 1, p}
    for q in qs:
        if not (1 <= q <= 2*p): continue
        for d in ds:
            if not (0 <= d <= p): continue
            total_c += 1
            if check_instance(p, q, d):
                violations.append(('boundary', p, q, d))
emit(f'(c) boundary sweeps (q in {{1,2,p/2,2p/3+-,2p-1,2p}}, d in {{0,1,p/2,p-1,p}}, '
     f'p incl. 2304 and 10^9): {total_c} instances, '
     f'{sum(1 for v in violations if v[0]=="boundary")} violations   [{time.time()-t0:.1f}s]')

emit()
if violations:
    emit('COUNTEREXAMPLES FOUND (first 20):')
    for v in violations[:20]:
        emit(f'    {v}')
verdict = 'PASS (no counterexample found)' if not violations else 'FAIL — COUNTEREXAMPLE'
emit('='*72)
emit(f'VERDICT C2 (Theorem 4.2 core inequality (4.5), all three branches): {verdict}')
emit(f'Total instances: {total_a + total_b + total_c}')
emit('='*72)

rep = '\n'.join(OUT)
print(rep)
here = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(here, 'results'), exist_ok=True)
with open(os.path.join(here, 'results', 'c2_margin_results.txt'), 'w', encoding='utf-8') as f:
    f.write(rep + '\n')
sys.exit(0 if not violations else 1)
