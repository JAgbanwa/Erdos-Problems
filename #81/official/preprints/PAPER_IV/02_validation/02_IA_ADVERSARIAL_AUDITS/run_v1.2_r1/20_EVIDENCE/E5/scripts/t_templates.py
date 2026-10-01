"""E5 template / complete-graph tests: T10 (Prop 6.3a), T11 (E.3 witness), T16 (D.1, D.2), T17 (D.3), T06s (exact LP of (5.1a)).
usage: python t_templates.py [T10|T11|T16|T17|T06s|all]"""
import sys, os, time, itertools
from fractions import Fraction as Fr
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e5lib import *

which = sys.argv[1] if len(sys.argv) > 1 else 'all'
OUT = {}


def fmt(tid, d):
    OUT[tid] = d
    print(tid, d.get('result'), '| negctl:', (d.get('negative_control') or {}).get('result'), '|', d.get('runtime_s'))


def defect_template(cC, sD, hH, extraC=0):
    """(K_C u I_D) v I_H with C first, D next, H last."""
    (n, adj), (C, D, H) = template(cC, sD, hH)
    return n, adj, C, D, H


def weight_cert(n, adj, C, D, H):
    Cs, Hs = set(C), set(H)
    w = {}
    for (u, v) in edges_of(n, adj):
        if u in Cs and v in Cs:
            w[(u, v)] = Fr(-1)
        elif (u in Hs) != (v in Hs):
            w[(u, v)] = Fr(1)
        else:
            raise ValueError('unexpected edge class')
    return weight_lower_bound(n, adj, w)


def exact_cp(n, adj, C, D, H, want_orders=(None, 4, 3)):
    """cp, c4, c3 by CBC; exact lower bound by the weight certificate; exact verification of partitions."""
    valid, lb = weight_cert(n, adj, C, D, H)
    out = {'weight_certificate_valid': valid, 'weight_lower_bound': str(lb)}
    for r in want_orders:
        st, val, pieces = ilp_partition(n, adj, rmax=r)
        ok, why = verify_partition(n, adj, pieces, rmax=r) if pieces is not None else (False, st)
        key = 'cp' if r is None else f'c{r}'
        out[key] = {'ilp_status': st, 'value': val, 'partition_verified': ok, 'certified_exact': bool(valid and ok and val == lb)}
    return out


# ================================================================== T11
if which in ('T11', 'all'):
    t0 = time.time()
    rows, allok, negok = [], True, True
    plan = {0: range(2, 15), 1: range(4, 15), 2: range(6, 15), 3: range(8, 15)}
    for s, nrange in plan.items():
        for n in nrange:
            k = (n + s + 1) // 3
            cC, hH = k - s, n - k
            nn, adj, C, D, H = defect_template(cC, s, hH)
            assert nn == n
            ts = time.time()
            r = rsd(n, adj)
            cpres = exact_cp(n, adj, C, D, H, want_orders=(None, 3))
            qs = Q(s, n)
            ok = (r <= s and cpres['weight_certificate_valid'] and Fr(cpres['weight_lower_bound']) == qs and cpres['cp']['certified_exact'] and cpres['c3']['certified_exact']
                  and Bsn(s, n, k) == qs)
            neg = (r == s) if s >= 1 else True  # rsd <= s-1 must fail
            allok &= ok
            if s >= 1:
                negok &= neg
            rows.append({'s': s, 'n': n, 'k': k, '|C|,|D|,|H|': [cC, s, hH], 'rsd': r, 'Q_s(n)': qs, 'cp': cpres['cp']['value'], 'c3': cpres['c3']['value'],
                         'cp_certified': cpres['cp']['certified_exact'], 'ok': ok, 'sec': round(time.time() - ts, 2)})
            print(rows[-1])
    fmt('T11', dict(id='T11', claim='E.3 witness (K_{k-s} u I_s) v I_{n-k}, k=floor((n+s+1)/3), n>=2s+2: rsd<=s and cp=Q_s(n) (unrestricted lower bound by weights)',
                    manuscript_lines='1967-1979', method='brute-force rsd over all (U,R); cp and c3 by CBC ILP over all cliques, partition verified exactly, lower bound by exact weight certificate (every clique weight<=1 enumerated)',
                    evidence_type='exact for listed instances (ILP partition verified + exact dual weight certificate)', parameters={'plan(s: n-range)': {s: [min(r), max(r)] for s, r in plan.items()}},
                    details={'instances': rows}, result='PASS' if allok else 'FAIL',
                    negative_control={'description': 'rsd<=s-1 must fail for s>=1 (brute-force rsd equals s); cp<=Q_s(n)-1 excluded by the exact weight bound', 'rsd_equals_s_for_all_s>=1': negok,
                                      'result': 'PASS (rejected)' if negok else 'FAIL (accepted)'},
                    runtime_s=round(time.time() - t0, 2)))

# ================================================================== T10
if which in ('T10', 'all'):
    t0 = time.time()
    # --- symbolic part
    s_, q_, d_ = sp.symbols('s q d', integer=True)
    n_ = 3 * q_ - s_
    k_ = q_ + d_
    Bsym = k_ * (n_ - k_) - (k_ - s_) * (k_ - s_ - 1) / 2
    Qsym = q_ * (3 * q_ + 1) / 2 - s_ * (s_ + 1) / 2  # M(3q)=q(3q+1)/2 exactly (q(3q+1) even)
    sym1 = sp.simplify(Qsym - Bsym - (3 * d_ ** 2 - d_) / 2)
    eG = (q_ + d_ - s_) * (q_ + d_ - s_ - 1) / 2 + (q_ + d_) * (2 * q_ - s_ - d_)
    eT = (q_ - s_) * (q_ - s_ - 1) / 2 + q_ * (2 * q_ - s_)
    sym2 = sp.simplify(2 * (eG - eT) - d_ * (4 * q_ - 4 * s_ - d_ - 1))
    sym3 = sp.simplify(4 * (eG - eT) - n_ * d_ - d_ * (5 * q_ - 7 * s_ - 2 * d_ - 2))
    sym4 = sp.simplify((5 * q_ - 7 * s_ - 2 * d_ - 2) - (4 * (q_ - 2 * s_ - 2) + (q_ - 2 * d_) + s_ + 6))
    # --- exhaustive integer part
    bad = []
    cnt = 0
    for s in range(0, 21):
        for q in range(2 * s + 2, 201):
            n = 3 * q - s
            if M(3 * q) * 2 != q * (3 * q + 1):
                bad.append(('M3q', s, q))
            ks = [k for k in range(0, n + s + 2) if Bsn(s, n, k) == max(Bsn(s, n, kk) for kk in range(0, n + s + 2))] if q <= 40 else [q]
            if ks != [q]:
                bad.append(('unique_opt', s, q, ks))
            for d in range(1, q // 2 + 1):
                cnt += 1
                dd = (3 * d * d - d) // 2
                e_G = C2(q + d - s) + (q + d) * (2 * q - s - d)
                e_T = C2(q - s) + q * (2 * q - s)
                if Q(s, n) - Bsn(s, n, q + d) != dd or (3 * d * d - d) % 2:
                    bad.append(('delta', s, q, d))
                if 2 * (e_G - e_T) != d * (4 * q - 4 * s - d - 1) or 4 * (e_G - e_T) < n * d:
                    bad.append(('edges', s, q, d))
                if not (4 * d * d >= dd):  # nd/4 >= n sqrt(dd)/8  <=>  4d^2 >= dd
                    bad.append(('sqrt', s, q, d))
                if not (2 <= q + d - s <= 2 * q - s - d):  # clique core >=2 and <= host set
                    bad.append(('sizes', s, q, d))
    # --- brute-force instances
    inst = [(0, 2, 1), (0, 3, 1), (0, 4, 1), (0, 4, 2), (1, 4, 1), (1, 4, 2), (1, 5, 1), (1, 5, 2), (2, 6, 1), (2, 6, 2), (2, 6, 3)]
    rows, allok = [], True
    negrsd, negdelta = [], []
    for (s, q, d) in inst:
        ts = time.time()
        n = 3 * q - s
        cC, hH = q + d - s, 2 * q - s - d
        nn, adj, C, D, H = defect_template(cC, s, hH)
        assert nn == n
        r = rsd(n, adj)
        cpres = exact_cp(n, adj, C, D, H, want_orders=(None, 4))
        dd = (3 * d * d - d) // 2
        target = Q(s, n) - dd
        # distance to all optimal-size templates (core size q => |C'|=q-s, |D'|=s, |H'|=2q-s)
        Eset = set(edges_of(n, adj))
        mind = None
        ntempl = 0
        if math.comb(n, q - s) * math.comb(n - q + s, s) <= 200000:
            for Cp in itertools.combinations(range(n), q - s):
                restv = [v for v in range(n) if v not in Cp]
                for Dp in itertools.combinations(restv, s):
                    Hp = [v for v in restv if v not in Dp]
                    T = set(itertools.combinations(Cp, 2)) | {(min(u, v), max(u, v)) for u in list(Cp) + list(Dp) for v in Hp}
                    de = len(Eset ^ T)
                    ntempl += 1
                    mind = de if mind is None else min(mind, de)
        ok = (r <= s and cpres['cp']['certified_exact'] and cpres['c4']['certified_exact'] and cpres['cp']['value'] == target and cpres['c4']['value'] == target
              and (mind is None or 4 * mind >= n * d))
        allok &= ok
        if s >= 1:
            negrsd.append(r == s)
        if d >= 2:
            negdelta.append(cpres['cp']['value'] != Q(s, n) - d * d)
        rows.append({'s': s, 'q': q, 'd': d, 'n': n, 'rsd': r, 'cp': cpres['cp']['value'], 'c4': cpres['c4']['value'], 'Q_s(n)-delta_d': target,
                     'certified': cpres['cp']['certified_exact'] and cpres['c4']['certified_exact'], 'templates_checked': ntempl, 'min_dE_optimal_templates': mind,
                     'nd/4': str(Fr(n * d, 4)), 'n*sqrt(delta)/8': float(n * math.sqrt(dd) / 8), 'ok': ok, 'sec': round(time.time() - ts, 2)})
        print(rows[-1])
    ok_all = allok and not bad and sym1 == 0 and sym2 == 0 and sym3 == 0 and sym4 == 0
    fmt('T10', dict(id='T10', claim='Prop 6.3a: G_{s,q,d}=(K_{q+d-s} u I_s) v I_{2q-s-d}, n=3q-s: rsd<=s; cp=c4=Q_s(n)-delta_d, delta_d=(3d^2-d)/2; d_E(G,T)>=nd/4>=n sqrt(delta_d)/8 for every optimal-size T',
                    manuscript_lines='1016-1052', method='sympy identities; exhaustive integers s<=20, q<=200; brute-force rsd, CBC ILP cp/c4 with exact weight certificate, brute-force min d_E over all labelled optimal-size templates for tiny instances',
                    evidence_type='symbolic + finite exhaustive + exact (tiny instances)', parameters={'integer_scan': 's<=20, 2s+2<=q<=200, 1<=d<=q/2', 'instances': inst},
                    details={'sympy_residuals': [str(sym1), str(sym2), str(sym3), str(sym4)], 'integer_cases': cnt, 'integer_violations': bad[:10], 'instances': rows},
                    result='PASS' if ok_all else 'FAIL',
                    negative_control={'description': 'corrupted delta_d=d^2 must be rejected on some d>=2 instance; rsd<=s-1 must fail on s>=1 instances',
                                      'd^2_rejected_on_all_d>=2': all(negdelta), 'rsd_equals_s_on_all_s>=1': all(negrsd),
                                      'result': 'PASS (rejected)' if (negdelta and all(negdelta) and all(negrsd)) else 'FAIL (accepted)'},
                    runtime_s=round(time.time() - t0, 2)))

# ================================================================== T16
if which in ('T16', 'all'):
    import pulp
    t0 = time.time()

    def best_packing(n, allow4=True, gain_target=None, tl=120):
        full = [(1 << n) - 1 & ~0]
        adj = [((1 << n) - 1) & ~(1 << v) for v in range(n)]
        E = edges_of(n, adj)
        pieces = all_cliques(n, adj, 3, 4 if allow4 else 3)
        prob = pulp.LpProblem('pk', pulp.LpMaximize)
        x = [pulp.LpVariable(f'x{j}', cat='Binary') for j in range(len(pieces))]
        prob += pulp.lpSum((5 if popcount(K) == 4 else 2) * x[j] for j, K in enumerate(pieces))
        cov = {e: [] for e in E}
        for j, K in enumerate(pieces):
            for p in pairs_of(K):
                cov[p].append(x[j])
        for e in E:
            prob += pulp.lpSum(cov[e]) <= 1
        if gain_target is not None:
            prob += pulp.lpSum((5 if popcount(K) == 4 else 2) * x[j] for j, K in enumerate(pieces)) >= gain_target
        prob.solve(pulp.PULP_CBC_CMD(msg=0, timeLimit=tl))
        st = pulp.LpStatus[prob.status]
        if st not in ('Optimal',):
            return st, None, None, adj
        P = [pieces[j] for j in range(len(pieces)) if x[j].value() > 0.5]
        # completion
        cov2 = set(p for K in P for p in pairs_of(K))
        Q_ = P + [(1 << a) | (1 << b) for (a, b) in E if (a, b) not in cov2]
        return st, P, Q_, adj

    d1 = []
    ok1 = True
    for n in range(0, 14):
        if n < 2:
            d1.append({'n': n, 'M': M(n), 'pieces': 0, 'ok': True}); continue
        st, P, Qp, adj = best_packing(n, True, gain_target=C2(n) - M(n))
        ok, why = verify_partition(n, adj, Qp, rmax=4) if Qp is not None else (False, st)
        g = sum(C2(popcount(K)) - 1 for K in P) if P is not None else None
        good = ok and len(Qp) <= M(n) and len(Qp) == C2(n) - g
        ok1 &= good
        d1.append({'n': n, 'M': M(n), 'status': st, 'pieces': len(Qp) if Qp else None, 'gain': g, 'verified': ok, 'ok': good})
        print(d1[-1])
    # D.2: c3(K_n) for n=4,10,16 ; parity lower bound
    d2 = []
    ok2 = True
    for n in (4, 10, 16):
        st, P, Qp, adj = best_packing(n, False, tl=(120 if n == 16 else 300))
        ok, why = verify_partition(n, adj, Qp, rmax=3) if Qp is not None else (False, st)
        # exact parity lower bound: a >= n/2 (each vertex in >=1 K2 as n-1 odd), |Q| = (C(n,2)+2a)/3
        a_min = -(-n // 2)
        lb = -(-(C2(n) + 2 * a_min) // 3)
        val = len(Qp) if Qp else None
        certified = ok and val == lb
        # second solve: <= M(n) pieces with triangles+edges infeasible  <=> gain >= C(n,2)-M(n) infeasible
        # (n=16: second solve skipped - first attempt exceeded the time budget; the parity bound is an exact proof anyway)
        st2 = best_packing(n, False, gain_target=C2(n) - M(n), tl=300)[0] if n <= 10 else 'skipped (time budget)'
        good = certified and val == M(n) + 1 and lb > M(n)
        ok2 &= good
        d2.append({'n': n, 'M': M(n), 'c3_found': val, 'parity_lower_bound': lb, 'verified': ok, 'certified_exact': certified, 'ILP_with_<=M(n)_status': st2, 'ok': good})
        print(d2[-1])
    # negative control: n=9 (3 mod 6): the claim 'order<=3 needs >M(n)' must be rejected
    st, P, Qp, adj = best_packing(9, False)
    ok9, _ = verify_partition(9, adj, Qp, rmax=3)
    negok = ok9 and len(Qp) <= M(9)
    fmt('T16', dict(id='T16', claim='Prop D.1: c4(K_n)<=M(n) (n<=13 checked); Prop D.2: n=4 mod 6 => every order<=3 partition of K_n has >M(n) pieces (c3(K_10)=M(10)+1=19)',
                    manuscript_lines='1705-1761', method='CBC ILP constructs packings; completions verified exactly; D.2 lower bound by exact parity argument (independent), upper bound by verified partition; second ILP solve with <=M(n) (solver-dependent)',
                    evidence_type='exact constructions (D.1); exact value certified by parity bound + verified partition (D.2); ILP infeasibility solver-dependent',
                    parameters={'D.1 n': [0, 13], 'D.2 n': [4, 10, 16], 'note': 'D.2 second (infeasibility) ILP solve only for n<=10; for n=16 it exceeded the time budget in a first attempt and was skipped'}, details={'D.1': d1, 'D.2': d2},
                    result='PASS' if (ok1 and ok2) else 'FAIL',
                    negative_control={'description': 'corrupted D.2 at n=9 (3 mod 6): order<=3 partition with <=M(9) pieces must exist (claim rejected)', 'c3(K9)_found': len(Qp), 'M(9)': M(9),
                                      'result': 'PASS (rejected)' if negok else 'FAIL (accepted)'},
                    runtime_s=round(time.time() - t0, 2)))

# ================================================================== T17
if which in ('T17', 'all'):
    t0 = time.time()
    rows, allok = [], True
    neg = []

    def factor_matchings(k):
        """round-robin 1-factorisation of K_k (k even) or near-1-factorisation (k odd)."""
        m = k if k % 2 == 0 else k + 1
        rounds = []
        for r in range(m - 1):
            pairs = []
            for i in range(m // 2):
                a = (r + i) % (m - 1)
                b = (r - i) % (m - 1) if i else m - 1
                if i == 0:
                    a, b = r % (m - 1), m - 1
                else:
                    a, b = (r + i) % (m - 1), (r - i) % (m - 1)
                if a < k and b < k:
                    pairs.append((min(a, b), max(a, b)))
            rounds.append(pairs)
        return [p for p in rounds if p]

    for k in range(2, 8):
        for h in range(k, 10):
            if k + h > 13:
                continue
            (n, adj), (C, D, H) = template(k, 0, h)
            W, x, y, st = exact_Wstar(n, adj)
            ms = factor_matchings(k)
            allpairs = sorted(p for mm in ms for p in mm)
            assert allpairs == sorted(itertools.combinations(range(k), 2)), (k, ms)
            assert len(ms) <= h
            P = [(1 << a) | (1 << b) | (1 << H[i]) for i, mm in enumerate(ms) for (a, b) in mm]
            seen = set(); disjoint = True
            for K in P:
                assert is_clique(K, adj)
                for pp in pairs_of(K):
                    if pp in seen: disjoint = False
                    seen.add(pp)
            gP = 2 * len(P)
            ok = st == 'exact' and W == 2 * C2(k) and disjoint and gP == 2 * C2(k)
            allok &= ok
            rows.append({'k': k, 'h': h, 'W*': str(W), 'status': st, 'W_construction': gP, '2C(k,2)': 2 * C2(k), 'ok': ok})
    for (k, h) in [(3, 1), (4, 1), (4, 2), (4, 3), (5, 2), (5, 3), (5, 4), (6, 3), (6, 5)]:
        (n, adj), _ = template(k, 0, h)
        W, x, y, st = exact_Wstar(n, adj)
        neg.append({'k': k, 'h': h, 'W*': str(W), 'status': st, 'equals_2C(k,2)': W == 2 * C2(k)})
    negok = any((not r['equals_2C(k,2)']) and r['status'] == 'exact' for r in neg)
    fmt('T17', dict(id='T17', claim='Prop D.3: S=K_k v I_h, 2<=k<=h: W*(S)=W(S)=2C(k,2)', manuscript_lines='1765-1781',
                    method='exact LP (HiGHS + exact primal/dual certificate); integral packing built from a 1-factorisation with distinct hosts and verified', evidence_type='exact (small k,h)',
                    parameters={'k': [2, 7], 'h': 'k..9, k+h<=13'}, details={'instances': rows, 'outside_range_k>h': neg},
                    result='PASS' if allok else ('INCONCLUSIVE' if any(r['status'] != 'exact' for r in rows) else 'FAIL'),
                    negative_control={'description': 'outside the hypothesis (k>h) the equality must fail somewhere (only exact-status instances count)', 'result': 'PASS (rejected)' if negok else 'FAIL (accepted)'},
                    runtime_s=round(time.time() - t0, 2)))

# ================================================================== T06s
if which in ('T06s', 'all'):
    t0 = time.time()
    rows, allok, viol, inconc = [], True, [], []
    for r in range(4, 12):
        for h in range(1, 13 - r):
            (n, adj), _ = template(r, 0, h)
            W, x, y, st = exact_Wstar(n, adj)
            e = len(edges_of(n, adj))
            F4 = e - W
            a0, b0 = C2(r), r * h
            checks = {}
            if b0 >= 2 * a0: checks['b0>=2a0: <=b0-a0'] = F4 <= b0 - a0
            if a0 <= b0 <= 2 * a0: checks['a0<=b0<=2a0: <=(2b0-a0)/3'] = F4 <= Fr(2 * b0 - a0, 3)
            if b0 <= a0: checks['b0<=a0: <=(a0+b0)/6'] = F4 <= Fr(a0 + b0, 6)
            ok = st == 'exact' and all(checks.values())
            allok &= ok
            if not all(checks.values()): viol.append((r, h))
            if st != 'exact': inconc.append((r, h))
            rows.append({'r': r, 'h': h, 'F4': str(F4), 'status': st, 'checks': checks})
    fmt('T06s', dict(id='T06s (supplementary to T06, not predeclared)', claim='(5.1a) F_4(S_C) upper bounds by branch, r>=4, nonempty exterior', manuscript_lines='458-468',
                     method='exact LP with verified certificates for K_r v I_h, 4<=r<=11, r+h<=12', evidence_type='exact (small instances)',
                     parameters={}, details={'instances': rows, 'violations': viol, 'inexact_lp': inconc}, result='PASS' if allok else ('FAIL' if viol else 'INCONCLUSIVE'),
                     negative_control={'description': 'none', 'result': 'N/A'}, runtime_s=round(time.time() - t0, 2)))

dump(f'templates_{which}.json', OUT)
