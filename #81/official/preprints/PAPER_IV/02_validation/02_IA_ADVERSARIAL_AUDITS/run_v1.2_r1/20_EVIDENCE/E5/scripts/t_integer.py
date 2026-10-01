"""E5 integer-exhaustive tests: T07, T08, T09, T20 (arithmetic parts (E.2e),(E.13)), T23 (G.5 algebra)."""
import sys, os, time
from fractions import Fraction as Fr
import z3
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e5lib import *

OUT = {}


def rec(tid, **kw):
    kw['id'] = tid
    OUT[tid] = kw
    print(tid, kw.get('result'), '| negctl:', (kw.get('negative_control') or {}).get('result'))


def z3_unsat(premises, neg):
    s = z3.Solver(); s.add(*premises); s.add(neg)
    r = s.check()
    return str(r), (str(s.model()) if r == z3.sat else None)


def f(n, k):
    return k * (n - k) - C2(k)


def opt_cores_64(n):
    r, e = divmod(n, 3)
    return {0: {r}, 1: {r, r + 1}, 2: {r + 1}}[e]


# ------------------------------------------------------------------ T07
t0 = time.time()
NM = 400
bad = {'6.3': [], '6.4': [], 'ceil': [], 'D.8': [], 'D.8zero': [], 'E.5': [], 'E.3': [], 'Qs>=B': []}
cnt = {k: 0 for k in bad}
for n in range(0, NM + 1):
    for k in range(-n - 2, 2 * n + 3):  # all integers in a wide window ("subtraction interpreted in the integers")
        cnt['6.3'] += 1
        if 6 * f(n, k) + (n - 3 * k) * (n - 3 * k + 1) != n * (n + 1):
            bad['6.3'].append((n, k))
    opt = {k for k in range(2, n + 1) if k <= n - k and f(n, k) == M(n)}
    cnt['6.4'] += 1
    if opt != {k for k in opt_cores_64(n) if 2 <= k <= n - k}:
        bad['6.4'].append((n, sorted(opt)))
    if n >= 6:
        k = -(-n // 3)
        cnt['ceil'] += 1
        if not (k in opt_cores_64(n) and 2 <= k <= n - k):
            bad['ceil'].append(n)
    for k in range(0, n + 1):
        if C2(k) <= k * (n - k):
            dd = n - 3 * k if 3 * k <= n else 3 * k - n - 1
            cnt['D.8'] += 1
            if dd < 0 or M(n) != Bn(n, k) + M(dd):
                bad['D.8'].append((n, k))
            cnt['D.8zero'] += 1
            if (M(n) - Bn(n, k) == 0) != (dd <= 1):
                bad['D.8zero'].append((n, k))
SM = 60
for s in range(0, SM + 1):
    for n in range(2 * s + 2, NM + 1):
        k = (n + s + 1) // 3
        cnt['E.5'] += 1
        if Bsn(s, n, k) != Q(s, n) or not (0 <= k - s and k <= n):
            bad['E.5'].append((s, n))
    for n in range(1, NM + 1):
        cnt['E.3'] += 1
        if Q(s, n) - Q(s, n - 1) != (n + s + 1) // 3:
            bad['E.3'].append((s, n))
        for k in range(0, n + 1):
            cnt['Qs>=B'] += 1
            if Q(s, n) < Bsn(s, n, k):
                bad['Qs>=B'].append((s, n, k))
ok = all(len(v) == 0 for v in bad.values())
# negative controls
neg1 = any(6 * f(n, k) + (n - 3 * k) * (n - 3 * k - 1) != n * (n + 1) for n in range(0, 50) for k in range(0, n + 1))
neg2 = any(Q(s, n) - Q(s, n - 1) != (n + s) // 3 for s in range(0, 10) for n in range(1, 60))
rec('T07', claim='(6.3)/(6.8) 6f+(n-3k)(n-3k+1)=n(n+1); (6.4) optimal cores; k=ceil(n/3) optimal (n>=6); (D.8) M(n)=B_n(k)+M(d_{n,k}) and zero reserve iff d<=1; E.5 B_{s,n}(floor((n+s+1)/3))=Q_s(n) (n>=2s+2); (E.3) Q_s(n)-Q_s(n-1)=floor((n+s+1)/3); Q_s(n)>=B_{s,n}(k) all k',
    manuscript_lines='692-695, 759-775, 881-895, 1785-1796, 1953-1956, 1969-1979', method='exhaustive exact integer arithmetic', evidence_type='finite exhaustive',
    parameters={'n': [0, NM], 'k(6.3)': '[-n-2, 2n+2]', 's': [0, SM]}, details={'checked_counts': cnt, 'violations_first5': {k: v[:5] for k, v in bad.items()},
                'note_E.3': 'holds for every n>=1 in range, not only for sufficiently large n'},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': 'corrupted (6.3) with (n-3k)(n-3k-1) and corrupted (E.3) floor((n+s)/3) must fail somewhere', 'corrupt_6.3_fails': neg1, 'corrupt_E.3_fails': neg2,
                      'result': 'PASS (rejected)' if (neg1 and neg2) else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T08
t0 = time.time()
AB = 60
viol = []
zeros = []
eq10 = []
for a in range(0, AB + 1):
    for b in range(0, AB + 1):
        if a + b < 2:
            continue
        d1 = 1 + C2(a) + 3 * C2(b) - a * b
        d2num = (a - b) * (a - b - 1)  # /2
        if 2 * d1 != d2num + 2 * (b - 1) ** 2:
            viol.append(('identity', a, b))
        if d1 < 0:
            viol.append(('neg', a, b))
        if d1 == 0:
            zeros.append((a, b))
        if d1 > 0:
            if C2(a + b) > 10 * d1:
                viol.append(('edge', a, b))
            if C2(a + b) == 10 * d1:
                eq10.append((a, b))
ok = len(viol) == 0 and sorted(zeros) == [(1, 1), (2, 1)] and (3, 2) in eq10
neg9 = [(a, b) for a in range(0, AB + 1) for b in range(0, AB + 1) if a + b >= 2 and (1 + C2(a) + 3 * C2(b) - a * b) > 0 and C2(a + b) > 9 * (1 + C2(a) + 3 * C2(b) - a * b)]
rec('T08', claim='(6.7a) d_R=1+C(a,2)+3C(b,2)-ab=(a-b)(a-b-1)/2+(b-1)^2 >=0; zero iff canonical (a,b) in {(1,1),(2,1)}; C(a+b,2)<=10 d_R when d_R>0; sharp at (3,2)',
    manuscript_lines='862-877, 2253', method='exhaustive exact integers', evidence_type='finite exhaustive', parameters={'a,b': [0, AB]},
    details={'violations': viol[:10], 'zero_defect_profiles': zeros, 'equality_profiles_C(a+b,2)=10d': eq10},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': 'factor 9 must fail somewhere', 'violating_profiles_factor9': neg9[:10],
                      'result': 'PASS (rejected)' if neg9 else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T09
t0 = time.time()
S9, N9 = 20, 300
viol_adm, viol_all, argmax_bad = [], [], []
cnt_adm = cnt_all = 0
for s in range(0, S9 + 1):
    for n in range(0, N9 + 1):
        x = Fr(2 * (n + s) + 1, 6)
        cands = [x.numerator // x.denominator, x.numerator // x.denominator + 1]
        dmin = min(abs(c - x) for c in cands)
        K = [c for c in cands if abs(c - x) == dmin]
        # consistency: K = integer argmax of B_{s,n}(k)
        rng = range(-5, n + s + 6)
        mx = max(Bsn(s, n, k) for k in rng)
        if sorted(k for k in rng if Bsn(s, n, k) == mx) != sorted(K) or mx != Q(s, n):
            argmax_bad.append((s, n))
        for k in range(0, n + 1):
            dist = min(abs(k - c) for c in K)
            lhs, rhs = dist * dist, Q(s, n) - Bsn(s, n, k)
            cnt_all += 1
            if lhs > rhs:
                viol_all.append((s, n, k))
            if s + 2 <= k and k - s <= n - k:
                cnt_adm += 1
                if lhs > rhs:
                    viol_adm.append((s, n, k))
ok = not viol_adm and not viol_all and not argmax_bad
neg = []
for s in range(0, 6):
    for n in range(2 * s + 4, 60):
        x = Fr(2 * (n + s) + 1, 6)
        cands = [x.numerator // x.denominator, x.numerator // x.denominator + 1]
        dmin = min(abs(c - x) for c in cands)
        K = [c for c in cands if abs(c - x) == dmin]
        for k in range(s + 2, n + 1):
            if k - s <= n - k:
                dist = min(abs(k - c) for c in K)
                if 2 * dist * dist > Q(s, n) - Bsn(s, n, k):
                    neg.append((s, n, k))
rec('T09', claim='(6.19) dist(k,K_{s,n})^2 <= Q_s(n)-B_{s,n}(k), K_{s,n}=integers nearest (2(n+s)+1)/6', manuscript_lines='1004-1012',
    method='exhaustive exact integers; K computed with exact Fractions; also checked K = argmax_k B_{s,n}(k) and max = Q_s(n)', evidence_type='finite exhaustive',
    parameters={'s': [0, S9], 'n': [0, N9], 'admissible_k': 's+2<=k, k-s<=n-k', 'also_all_k': '0<=k<=n'},
    details={'checked_admissible': cnt_adm, 'checked_all_k': cnt_all, 'violations_admissible': viol_adm[:5], 'violations_all_k': viol_all[:5], 'argmax_mismatch': argmax_bad[:5]},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': 'corrupted 2*dist^2 <= Q_s-B must fail somewhere', 'violations_found': len(neg), 'example': neg[:3],
                      'result': 'PASS (rejected)' if neg else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T20 arithmetic part
t0 = time.time()
b1, b2 = [], []
c1 = c2 = 0
for s in range(0, 16):
    for c in range(0, 81):
        for b in range(0, 81):
            c1 += 1
            if c + b >= s + 2 and c * (b + s) > C2(c) + M(c + b + s):
                b1.append((s, c, b))
            if c + b >= s + 2:
                z = -(-(c + b + s) // 3)
                for tW in range(0, 31):
                    c2 += 1
                    if Q(s, c + b) + tW * z > Q(s, c + b + tW):
                        b2.append((s, c, b, tW))
# the first inequality of (E.2e) without the side condition
b1_all = [(s, c, b) for s in range(0, 16) for c in range(0, 81) for b in range(0, 81) if c * (b + s) > C2(c) + M(c + b + s)]
# (E.13): r in {0,s}; if r=s: c-s<=2E, c>=2s ; n<=4c  =>  r n <= 16 s E
e13 = {}
neg15 = {}
for s in range(0, 31):
    cc, EE, nn = z3.Reals('cc EE nn')
    prem = [EE >= 0, cc >= 2 * s, cc - s <= 2 * EE, nn <= 4 * cc, nn >= 0]
    e13[s] = z3_unsat(prem, s * nn > 16 * s * EE)[0]
    neg15[s] = z3_unsat(prem, s * nn > 15 * s * EE)[0]
ok = not b1 and not b2 and all(v == 'unsat' for v in e13.values())
rec('T20a', claim='(E.2e) c(b+s)<=C(c,2)+M(c+b+s) and Q_s(c+b)+t_W ceil((c+b+s)/3)<=Q_s(c+b+t_W) (c+b>=s+2); (E.13) r n<=16sE from c-s<=2E, c>=2s, n<=4c',
    manuscript_lines='1931-1940, 2083-2086', method='exhaustive integers (E.2e); z3 LRA per fixed s (E.13)', evidence_type='finite exhaustive + exact (LRA)',
    parameters={'s': [0, 15], 'c,b': [0, 80], 't_W': [0, 30], 'E.13 s': [0, 30]},
    details={'E.2e_first_checked': c1, 'E.2e_second_checked': c2, 'viol_first': b1[:5], 'viol_second': b2[:5], 'first_ineq_holds_without_side_condition': not b1_all,
             'E.13_unsat_all_s': all(v == 'unsat' for v in e13.values())},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': 'constant 15 in (E.13) must be refutable for s>=1 (equality case c=2s, E=s/2, n=4c)', 'sat_for_s>=1': all(neg15[s] == 'sat' for s in range(1, 31)),
                      'result': 'PASS (rejected)' if all(neg15[s] == 'sat' for s in range(1, 31)) else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T23 algebra part (G.5)
t0 = time.time()
ep, nv, T = z3.Reals('ep nv T')
prem = [ep > 0, nv >= 2, T >= 0, ep * nv * nv / 30 - 1 <= T, T <= (2 * nv - 3) / 3]
r = z3_unsat(prem, nv > 20 / ep)
rn = z3_unsat(prem, nv > 19 / ep)
OUT['T23_G5'] = {'claim': '(G.5) eps n^2/30-1 <= T <= (2n-3)/3 => n <= 20/eps', 'z3': r[0], 'neg_19': rn[0], 'neg_model': rn[1], 'runtime_s': round(time.time() - t0, 3)}
print('T23_G5', r[0], rn[0])
dump('integer_tests.json', OUT)
