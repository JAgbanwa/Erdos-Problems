r"""
EXTERNAL ADVERSARIAL AUDIT — Block C, attack C4: Proposition 10.1 (effective corridor).

Part (i): p >= 36, 0 <= s <= 6 sqrt(p)  =>  Phi(G) <= n^2/6 + 2n.
Part (ii): p >= 2304, 6 sqrt(p) <= s <= p/8, d(v) > (2n-1)/6 + 1  =>  Phi(G) <= n^2/6.

These are FOR-ALL claims over split graphs; a computational audit can only
(a) probe adversarial concrete instances (a violation would REFUTE), and
(b) verify the analytic chain behind the bounds exactly (done in Block D:
    D12, D14, D15, D18, D20). Here we do (a) with explicit packing
    certificates, at true scale, including the boundary p = 2304 where the
    mesoscopic window [6 sqrt(p), p/8] degenerates to the single point s = 288.

Certificates: a packing is CONSTRUCTED (factorization assignment), then
edge-disjointness and membership are verified exactly with numpy uint8
edge-use counters; a verified packing of size >= (|E| - bound)/2 proves
Phi(G) <= bound for that instance.

Part (i) instances: p in {36, 49, 64, 100}, s in {0, 1, floor(6 sqrt p)},
  profiles: extremal d_i = p; common d_i = p - m; mixed random m_i <= s
  (when q >= r_p a factorization assignment optimized by Hungarian algorithm
  on the exact integer retained-edge matrix).
Part (ii) instances at p = 2304, s = 288, q = 4320, n = 6624:
  - common profile S_i = R, |R| = m for m in {0, 47, 94, 95}   (m <= 95 forced
    by the degree hypothesis: d > (2n-1)/6 + 1 <=> m_i <= 95 here)
  - construction: factorize K[Q] (b = p - m), assign r_b factors to distinct
    independent vertices (all retained: t_i = 0), pack QQI; then factorize
    K[R] and inject its rho-1 or rho factors into distinct colors z in Q,
    packing RRQ triangles {r1, r2, z} on fresh R-R and R-Q edges. Verified
    with numpy counters over all 12.2M edges.
  - a mixed profile with t_i > 0 (S_i strictly containing a common core is
    impossible with m<=95 forced; instead half the vertices use S_i = R, half
    use S_i = R' with |R'| = m, |R ∩ R'| = m - 5), packing QQI with losses
    only (IRQ/RRQ omitted — the certificate must still clear the bound).

Output: results/c4_corridor_results.txt
"""
import sys, os, math, random, time
import numpy as np
from fractions import Fraction as Q
from itertools import combinations

random.seed(2304)
OUT = []
def emit(x=''): OUT.append(str(x))
def C2i(x): return x*(x-1)//2
def rp_of(t):
    if t <= 1: return 0
    return t-1 if t % 2 == 0 else t

def factorization(p):
    """circle method; p even: p-1 perfect matchings; p odd: p near-perfect."""
    if p % 2 == 1:
        rounds = factorization(p + 1)
        return [[e for e in rd if p not in e] for rd in rounds]
    arr = list(range(p))
    rounds = []
    for _ in range(p - 1):
        prs = [(arr[0], arr[-1])] + [(arr[i], arr[-1-i]) for i in range(1, p//2)]
        rounds.append([tuple(sorted(x)) for x in prs])
        arr = [arr[0]] + [arr[-1]] + arr[1:-1]
    return rounds

failures = []

# ---------------------------------------------------------------- Part (i)
def hungarian(cost):
    """max-assignment via scipy (integer costs -> exact); rows=factors, cols=I-vertices."""
    from scipy.optimize import linear_sum_assignment
    c = np.asarray(cost, dtype=np.int64)
    r, cidx = linear_sum_assignment(-c)
    return list(zip(r.tolist(), cidx.tolist()))

def part_i_instance(p, s, profile_tag, neigh):
    q = 2*p - s
    n = p + q
    E = C2i(p) + sum(len(N) for N in neigh)
    bound_num = Q(n*n, 6) + 2*n                      # Phi <= this
    need = (Q(E) - bound_num)/2                      # nu3 >= this
    target = max(0, math.ceil(need))
    rounds = factorization(p)
    r_p = len(rounds)
    if q < r_p:
        return ('SKIP q<r_p', p, s, profile_tag)
    # retained-edge matrix: factor j x vertex i -> |F_j ∩ E(N_i)|
    Nsets = [set(N) for N in neigh]
    cost = [[sum(1 for (a, b) in rd if a in Ni and b in Ni) for Ni in Nsets]
            for rd in rounds]
    pack_size = 0
    used_cross_ok = True
    assign = hungarian(cost)
    for (j, i) in assign:
        pack_size += cost[j][i]
    # verify exactly: build packing & numpy counters
    ecl = np.zeros((p, p), dtype=np.uint8)
    ecr = np.zeros((q, p), dtype=np.uint8)
    cnt = 0
    for (j, i) in assign:
        Ni = Nsets[i]
        for (a, b) in rounds[j]:
            if a in Ni and b in Ni:
                ecl[a, b] += 1
                ecr[i, a] += 1
                ecr[i, b] += 1
                cnt += 1
    okdisj = (ecl.max() <= 1) and (ecr.max() <= 1)
    okmem = all(ecr[i, a] == 0 or a in Nsets[i] for i in range(q) for a in range(p)
                if ecr[i, a])
    ok = okdisj and okmem and cnt == pack_size and Q(cnt) >= need
    return ('PASS' if ok else 'FAIL', p, s, profile_tag, f'nu3_cert={cnt}',
            f'needed>={need}', f'|E|={E}')

emit('--- Part (i): Phi <= n^2/6 + 2n on adversarial corridor instances ---')
t0 = time.time()
for p in (36, 49, 64, 100):
    smax = math.isqrt(36*p)
    for s in (0, 1, smax):
        q = 2*p - s
        profs = [('extremal d=p', [frozenset(range(p))]*q)]
        m = min(s, p)
        profs.append(('common d=p-m', [frozenset(range(p - m))]*q) if m else
                     ('common d=p', [frozenset(range(p))]*q))
        rnd = [frozenset(random.sample(range(p), p - random.randint(0, m))) for _ in range(q)]
        profs.append(('random m_i<=s', rnd))
        for tag, neigh in profs:
            res = part_i_instance(p, s, tag, neigh)
            emit(f'    {res}')
            if res[0] == 'FAIL': failures.append(res)
emit(f'[{time.time()-t0:.0f}s]')
emit()

# ---------------------------------------------------------------- Part (ii)
emit('--- Part (ii): Phi <= n^2/6 at p = 2304, s = 288 (the corridor threshold point) ---')

def part_ii_common(p, s, m):
    """Common profile S_i = R = {0..m-1}; certificate via K[Q]+K[R] factorizations."""
    q = 2*p - s; n = p + q
    d = p - m
    # degree hypothesis: d > (2n-1)/6 + 1 ?
    hyp = Q(d) > Q(2*n - 1, 6) + 1
    E = C2i(p) + q*d
    need = (Q(E) - Q(n*n, 6))/2
    target = max(0, math.ceil(need))
    R = list(range(m)); Qv = list(range(m, p)); b = len(Qv)
    rounds = factorization(b)                     # over 0..b-1 -> map to Qv
    r_b = len(rounds)
    assert q >= r_b
    # numpy edge counters
    ecl = np.zeros((p, p), dtype=np.uint8)        # clique edges (a<b)
    ecr = np.zeros((q, p), dtype=np.uint8)        # cross edges
    cnt = 0
    # QQI: factor j -> independent vertex j (t_i = 0: all edges retained)
    for j, rd in enumerate(rounds):
        for (a, b_) in rd:
            x, y = Qv[a], Qv[b_]
            ecl[min(x, y), max(x, y)] += 1
            ecr[j, x] += 1; ecr[j, y] += 1
            cnt += 1
    # RRQ: factorize K[R], inject factors into distinct colors z in Q
    if m >= 2:
        rrounds = factorization(m)
        assert len(rrounds) <= b
        for jz, rd in enumerate(rrounds):
            z = Qv[jz]
            for (a, b_) in rd:
                x, y = R[a], R[b_]
                ecl[min(x, y), max(x, y)] += 1
                ecl[min(x, z), max(x, z)] += 1
                ecl[min(y, z), max(y, z)] += 1
                cnt += 1
    okdisj = int(ecl.max()) <= 1 and int(ecr.max()) <= 1
    # membership: cross edges only to N_i = K \ R = Qv — by construction cross
    # edges go to Qv only; verified: columns 0..m-1 of ecr must be zero
    okmem = int(ecr[:, :m].max(initial=0)) == 0 if m else True
    ok = okdisj and okmem and Q(cnt) >= need
    return ok, dict(p=p, s=s, m=m, q=q, n=n, E=E, need=str(need), cert=cnt,
                    hyp_deg=bool(hyp), disj=okdisj, mem=okmem)

t0 = time.time()
for m in (0, 47, 94, 95):
    ok, info = part_ii_common(2304, 288, m)
    emit(f'    common m={m}: {"PASS" if ok else "FAIL"}  {info}')
    if not ok: failures.append(('part_ii_common', info))
emit(f'[{time.time()-t0:.0f}s]')

def part_ii_mixed(p, s, m, overlap):
    """Half of I uses S_i = R1 = {0..m-1}, half S_i = R2 (|R2| = m,
    |R1 ∩ R2| = overlap). Certificate follows the paper's own mechanism with
    center R = R1, Q = K \ R1, b = p - m:
      - factorize K[Q]; assign the r_b factors first to the t_i = 0 vertices
        (S_i = R1), the remainder to S_i = R2 vertices, DROPPING factor edges
        meeting T_i = R2 \ R1 (the QQI losses beta_i of §7.1);
      - RRQ: factorize K[R1], inject its factors into distinct colors z in Q
        (edges R1-R1 and R1-z are untouched by QQI). No IRQ family is used, so
        no forbidden-color deletion is needed. The certificate must still clear
        (|E| - n^2/6)/2."""
    q = 2*p - s; n = p + q; d = p - m
    hyp = Q(d) > Q(2*n - 1, 6) + 1
    R1 = sorted(range(m)); R2set = set(range(overlap)) | set(range(m, 2*m - overlap))
    T = sorted(R2set - set(R1))                       # petals of the second center
    Qv = [x for x in range(p) if x not in set(R1)]
    b = len(Qv)
    E = C2i(p) + q*d
    need = (Q(E) - Q(n*n, 6))/2
    rounds = factorization(b)
    r_b = len(rounds)
    assert q >= r_b
    nb_t0 = q // 2                                    # vertices with S_i = R1
    ecl = np.zeros((p, p), dtype=np.uint8)
    ecr = np.zeros((q, p), dtype=np.uint8)
    cnt = 0
    Tq = {Qv.index(x) for x in T}                     # T inside Q-indexing
    for j, rd in enumerate(rounds):
        i = j                                         # factor j -> vertex j
        drop_T = i >= nb_t0                           # S_i = R2 vertices drop T-edges
        for (a, b_) in rd:
            if drop_T and (a in Tq or b_ in Tq):
                continue
            x, y = Qv[a], Qv[b_]
            ecl[min(x, y), max(x, y)] += 1
            ecr[i, x] += 1; ecr[i, y] += 1
            cnt += 1
    if m >= 2:
        rrounds = factorization(m)
        assert len(rrounds) <= b
        for jz, rd in enumerate(rrounds):
            z = Qv[jz]
            for (a, b_) in rd:
                x, y = R1[a], R1[b_]
                ecl[min(x, y), max(x, y)] += 1
                ecl[min(x, z), max(x, z)] += 1
                ecl[min(y, z), max(y, z)] += 1
                cnt += 1
    okdisj = int(ecl.max()) <= 1 and int(ecr.max()) <= 1
    # membership: vertex i's cross edges must lie in N_i = K \ S_i
    bad_cols_1 = R1                                   # S = R1 vertices
    bad_cols_2 = sorted(R2set)                        # S = R2 vertices
    okmem = (int(ecr[:nb_t0, bad_cols_1].max(initial=0)) == 0 and
             int(ecr[nb_t0:, bad_cols_2].max(initial=0)) == 0)
    ok = okdisj and okmem and Q(cnt) >= need
    return ok, dict(p=p, s=s, m=m, overlap=overlap, E=E, need=str(need), cert=cnt,
                    hyp_deg=bool(hyp), disj=okdisj, mem=okmem)

t0 = time.time()
ok, info = part_ii_mixed(2304, 288, 94, 89)
emit(f'    mixed two-center m=94 overlap=89: {"PASS" if ok else "FAIL"}  {info}')
if not ok: failures.append(('part_ii_mixed', info))
emit(f'[{time.time()-t0:.0f}s]')
emit()

# window degeneracy observation at the boundary
lo = math.isqrt(36*2304); hi = 2304//8
emit(f'Note: at p = 2304 the window [6 sqrt p, p/8] = [{lo}, {hi}] '
     f'({"a single point" if lo == hi else "nonempty"}), as the threshold p=2304 predicts.')
emit()
emit('='*72)
emit(f"VERDICT C4: {'PASS — all corridor instances certified within the claimed bounds' if not failures else 'FAIL'}")
emit('='*72)

rep = '\n'.join(OUT)
print(rep)
here = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(here, 'results'), exist_ok=True)
with open(os.path.join(here, 'results', 'c4_corridor_results.txt'), 'w', encoding='utf-8') as f:
    f.write(rep + '\n')
sys.exit(0 if not failures else 1)
