"""E5 scalar / symbolic tests: T01-T06, T18, T19, T21 (symbolic part), T22, T24.
Exact rational arithmetic (fractions), sympy, z3 (linear/nonlinear real arithmetic)."""
import sys, time, math
from fractions import Fraction as Fr
import sympy as sp
import z3
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e5lib import *

OUT = {}


def rec(tid, **kw):
    kw['id'] = tid
    OUT[tid] = kw
    print(tid, kw.get('result'), '| negctl:', (kw.get('negative_control') or {}).get('result'))


def z3_unsat(premises, negated_conclusion):
    s = z3.Solver()
    s.add(*premises)
    s.add(negated_conclusion)
    r = s.check()
    return str(r), (s.model() if r == z3.sat else None)


eps0 = Fr(1, 10 ** 12)
eta0 = Fr(1, 10 ** 16)

# ------------------------------------------------------------------ T01
t0 = time.time()
def lhs46a(n):
    n = Fr(n)
    return Fr(16, 6) / n + 1 / n + Fr(16, 24) / (n * n)
rhs46a = eps0 - 16 * eta0
hold_4e12 = lhs46a(4 * 10 ** 12) < rhs46a
hold_36e11 = lhs46a(36 * 10 ** 11) < rhs46a
# equivalence of (4.6a) with 16D/n^2 < eps0 - 1/n (symbolic)
n_ = sp.symbols('n', positive=True)
e0, h0 = sp.Rational(1, 10 ** 12), sp.Rational(1, 10 ** 16)
D_ = h0 * n_ ** 2 + n_ / 6 + sp.Rational(1, 24)
diff_equiv = sp.simplify((16 * D_ / n_ ** 2 - (e0 - 1 / n_)) - ((sp.Rational(16, 6) / n_ + 1 / n_ + sp.Rational(16, 24) / n_ ** 2) - (e0 - 16 * h0)))
# monotonicity: derivative of LHS negative for n>0
dl = sp.diff(sp.Rational(16, 6) / n_ + 1 / n_ + sp.Rational(16, 24) / n_ ** 2, n_)
mono = all(c <= 0 for c in sp.Poly(sp.expand(dl * n_ ** 3), n_).all_coeffs())
# exact crossover: smallest integer n with LHS < RHS
lo, hi = 1, 10 ** 14
while lo < hi:
    mid = (lo + hi) // 2
    if lhs46a(mid) < rhs46a:
        hi = mid
    else:
        lo = mid + 1
crossover = lo
# negative control: budget factor 20 instead of 16 at n=4e12
def lhs_factor(n, F):
    n = Fr(n)
    return Fr(F, 6) / n + 1 / n + Fr(F, 24) / (n * n)
neg20 = lhs_factor(4 * 10 ** 12, 20) < eps0 - 20 * eta0
rec('T01', claim='(4.6a): 16/(6n)+1/n+16/(24n^2) < eps0-16eta0 holds at n=4e12, LHS decreasing, fails for n<=3.6e12',
    manuscript_lines='380-386', method='exact Fraction evaluation; sympy equivalence with 16D/n^2<eps0-1/n; sympy derivative sign; exact binary search for crossover',
    evidence_type='exact', parameters={'eps0': '1e-12', 'eta0': '1e-16'},
    details={'holds_at_4e12': hold_4e12, 'holds_at_3.6e12': hold_36e11, 'equivalence_residual': str(diff_equiv),
             'LHS_derivative_times_n3_coeffs_nonpositive': mono, 'exact_smallest_n_where_4.6a_holds': crossover,
             'LHS_at_4e12': str(float(lhs46a(4 * 10 ** 12))), 'RHS': str(float(rhs46a))},
    result='PASS' if (hold_4e12 and not hold_36e11 and diff_equiv == 0 and mono and 36 * 10 ** 11 < crossover <= 4 * 10 ** 12) else 'FAIL',
    negative_control={'description': 'old budget factor 20 (instead of 16) at n=4e12 must violate the contraction', 'accepted_by_test': neg20,
                      'result': 'PASS (rejected)' if not neg20 else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T02
t0 = time.time()
c1 = 16 * Fr(117, 1825); c2 = 16 * Fr(12687, 20000)
# LP: max m+10A s.t. (117/1825)m + (12687/20000)A <= 1 : vertices
lpval = max(1 / Fr(117, 1825), 10 / Fr(12687, 20000))
neg = 15 * Fr(117, 1825) > 1
rec('T02', claim='Lemma 4.2: 16*117/1825 > 1 and 16*12687/20000 > 10, hence m+10A <= 16D', manuscript_lines='366-368',
    method='exact Fraction; LP optimum of max m+10A s.t. (117/1825)m+(12687/20000)A<=D by vertex enumeration', evidence_type='exact',
    parameters={}, details={'16*117/1825': str(c1), '16*12687/20000': str(c2), 'LP max (m+10A)/D': str(lpval), 'LP max float': float(lpval)},
    result='PASS' if (c1 > 1 and c2 > 10 and lpval <= 16) else 'FAIL',
    negative_control={'description': 'factor 15 in place of 16 must fail (15*117/1825 > 1 false)', 'accepted_by_test': neg,
                      'result': 'PASS (rejected)' if not neg else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T03
t0 = time.time()
def lemma53(l_A, l_f, f_m=Fr(40, 73), f_A=Fr(-3, 40)):
    # |Q| = B + m - A - 2f + 2l ; l <= l_A A + l_f f ; f >= f_m m + f_A A (coefficient of f must be negative)
    cf = -2 + 2 * l_f
    cA = -1 + 2 * l_A
    assert cf < 0
    return 1 + cf * f_m, cA + cf * f_A, cA, cf
m1, A1, cA1, cf1 = lemma53(Fr(7, 40), Fr(1, 25))
m2, A2, cA2, cf2 = lemma53(Fr(11, 100), Fr(29, 1000))
# table 2 equivalences
tab_first = (Fr(2920) * Fr(40, 73) == 1600) and (Fr(2920) * Fr(3, 40) == 219)
tab_second = (Fr(200) * Fr(7, 40) == 35) and (Fr(200) * Fr(1, 25) == 8)
relax = Fr(11, 100) <= Fr(7, 40) and Fr(29, 1000) <= Fr(1, 25)
# (5.4a) symbolic
p, q, m, A, f, l, nn = sp.symbols('p q m A f l n')
lhs = sp.binomial(p, 2).expand(func=True) + p * q + m - A - 2 * (f + sp.binomial(p, 2).expand(func=True) - l)
rhs = (p * (nn - p) - p * (p - 1) / 2) + m - A - 2 * f + 2 * l
id54a = sp.simplify((lhs - rhs).subs(q, nn - p))
ok = (m1 == Fr(-19, 365) and A1 == Fr(-253, 500) and m2 == Fr(-117, 1825) and A2 == Fr(-12687, 20000)
      and cA1 == Fr(-13, 20) and cf1 == Fr(-48, 25) and cA2 == Fr(-39, 50) and cf2 == Fr(-971, 500)
      and tab_first and tab_second and relax and id54a == 0
      and Fr(19, 365) >= Fr(1, 20) and Fr(253, 500) >= Fr(1, 2) and Fr(117, 1825) > Fr(1, 16) and Fr(12687, 20000) > Fr(1, 2))
mneg, Aneg, _, _ = lemma53(Fr(8, 40), Fr(1, 25))
rec('T03', claim='Lemma 5.3 coefficients -19/365, -253/500 (from Table 2) and -117/1825, -12687/20000 (from l<=11A/100+29f/1000)',
    manuscript_lines='539-549, 655-688', method='exact recomputation of substitution chain; sympy check of (5.4a)', evidence_type='exact',
    parameters={}, details={'relaxed': [str(m1), str(A1)], 'strong': [str(m2), str(A2)], 'intermediate': [str(cA1), str(cf1), str(cA2), str(cf2)],
                            'table2_first_phase_equiv': tab_first, 'table2_second_phase_equiv': tab_second, '(5.4a)_residual': str(id54a)},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': 'corrupted second-phase ratio 8A/40 (instead of 7A/40) must NOT reproduce -253/500', 'observed_A_coeff': str(Aneg),
                      'result': 'PASS (rejected)' if Aneg != Fr(-253, 500) else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T04
t0 = time.time()
Q0 = Fr(87947, 44352); R0 = Fr(393, 100)
coefA = 1 / (48 * Q0) + (Fr(101, 100) * (Fr(1, 3) + Fr(1, 64)) + Fr(11, 2000)) / R0
coeff = 1 / (24 * Q0) + (Fr(101, 100) / 64 + Fr(11, 1000)) / R0
mid513 = Q0 ** 2 - Q0 / 1024
b512a = Fr(1, 64) + Fr(3, 57344)
# (5.12) t/a: t <= m/p + 1 < a/396 + 1 <= a/256 for a >= 1024; m/p < (a^2/400)/(99a/100) = a/396
t_ok = (Fr(1, 400) / Fr(99, 100) == Fr(1, 396)) and all(Fr(a, 396) + 1 <= Fr(a, 256) for a in (1024,)) and (Fr(1, 256) - Fr(1, 396)) * 1024 >= 1
# re-derivation of (5.14) from (5.11): coefficient of A and f after linearisation
# l <= (s/q)(A+2f) + [p((D+4t)A + 4tf) + (11/2000)a^2 (A+2f)] / (q(q-1))
sq = Fr(1, 48) / Q0  # s/q <= (s/a)/(q/a)
cA_re = sq + (Fr(101, 100) * (Fr(1, 3) + 4 * Fr(1, 256)) + Fr(11, 2000)) / R0
cf_re = 2 * sq + (Fr(101, 100) * 4 * Fr(1, 256) + 2 * Fr(11, 2000)) / R0
# monotonicity of x^2 - x/a in x for x>=Q0 (derivative 2x-1/a>0) : trivially true since Q0>1
ok = (coefA <= Fr(11, 100) and coeff <= Fr(29, 1000) and mid513 >= R0 and b512a < Fr(1, 48) and t_ok
      and cA_re == coefA and cf_re == coeff)
negR = (Q0 ** 2 - Q0 / 1024) >= Fr(394, 100)
negA = coefA <= Fr(1, 10)
rec('T04', claim='(5.14) coefficient bounds <=11/100 and <=29/1000; (5.13) q(q-1)/a^2 >= Q0^2-Q0/1024 >= 393/100; (5.12a) a/64+3a/57344 < a/48; (5.12) t/a<=1/256',
    manuscript_lines='618-655', method='exact Fraction evaluation; independent re-linearisation of (5.11) using (5.12)', evidence_type='exact (given the premises (5.12))',
    parameters={'Q0': '87947/44352', 'R0': '393/100'},
    details={'coefA': str(coefA), 'coefA_float': float(coefA), 'coeff': str(coeff), 'coeff_float': float(coeff), '(5.13)_middle': float(mid513),
             '(5.12a)_lhs_over_a': float(b512a), 'rederived_equal_to_printed': (cA_re == coefA and cf_re == coeff), 't_bound_ok': t_ok},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': 'corrupted R0=394/100 must fail (5.13); corrupted A-coefficient bound 1/10 must fail', 'R0_394_accepted': negR, 'coefA_le_1/10_accepted': negA,
                      'result': 'PASS (rejected)' if not (negR or negA) else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T05
t0 = time.time()
n, a, p, q = z3.Reals('n a p q')
prem = [n > 0, a >= z3.Q(33, 100) * n,
        n - 3 * a <= a / 64, 3 * a - n <= a / 64, 99 * a <= 100 * p, 48 * (2 * p - q) <= a, q == n - p]
concl = {'3267n<=10000p': 3267 * n <= 10000 * p, '3539p<=1188n': 3539 * p <= 1188 * n,
         '|3p-n|<=n/50': z3.And(3 * p - n <= n / 50, n - 3 * p <= n / 50)}
res5 = {k: z3_unsat(prem, z3.Not(c))[0] for k, c in concl.items()}
prem_min = [n > 0, a >= z3.Q(33, 100) * n, 99 * a <= 100 * p, 48 * (2 * p - q) <= a, q == n - p]
res5_min = {k: z3_unsat(prem_min, z3.Not(c))[0] for k, c in concl.items()}
# negative controls
neg1 = z3_unsat(prem, z3.Not(z3.And(3 * p - n <= n / 100, n - 3 * p <= n / 100)))
neg2 = z3_unsat([n > 0, a >= z3.Q(33, 100) * n, n - 3 * a <= a / 64, 3 * a - n <= a / 64, 48 * (2 * p - q) <= a, q == n - p], z3.Not(concl['3267n<=10000p']))
ok = all(v == 'unsat' for v in res5.values())
rec('T05', claim='Thm 5.0 window: a>=33n/100, 99a<=100p, 48(2p-q)_+<=a, q=n-p imply 3267n<=10000p, 3539p<=1188n, |3p-n|<=n/50',
    manuscript_lines='433, 440', method='z3 linear real arithmetic: premises AND NOT(conclusion) unsat; truncated premise replaced by weaker untruncated one (conservative)',
    evidence_type='exact (decision procedure for LRA)', parameters={},
    details={'with_|n-3a|<=a/64': res5, 'without_|n-3a|<=a/64': res5_min,
             'note': 'the upper bound uses 99a<=100p (a<=100p/99) together with 48(3p-n)<=a; |n-3a|<=a/64 is not needed'},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': 'corrupted conclusion |3p-n|<=n/100 must be refutable (sat); dropping 99a<=100p must make 3267n<=10000p refutable',
                      'corrupt_conclusion': neg1[0], 'drop_premise': neg2[0], 'counter_model_1': str(neg1[1]),
                      'result': 'PASS (rejected)' if (neg1[0] == 'sat' and neg2[0] == 'sat') else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T06
t0 = time.time()
d = {}
d['(a) 1e-12+1.5e-6 <= 0.33^2/65536'] = (Fr(1, 10 ** 12) + Fr(15, 10 ** 7)) <= Fr(33, 100) ** 2 / 65536
# (b) u(u+1)/2 <= eps0 n^2  =>  u <= 3n/(2e6)   (u>=0, n>0)
u, nv = z3.Reals('u nv')
d['(b) u(u+1)/2<=eps0 n^2 => u<=3n/2e6 (z3 NRA)'] = z3_unsat([u >= 0, nv > 0, u * (u + 1) / 2 <= z3.Q(1, 10 ** 12) * nv * nv], u > z3.Q(3, 2 * 10 ** 6) * nv)[0] == 'unsat'
d['(b\') exact: (1.5e-6)^2 > 2e-12'] = Fr(15, 10 ** 7) ** 2 > 2 * Fr(1, 10 ** 12)
d['(c) 7/2-129/64 = 95/64'] = Fr(7, 2) - Fr(129, 64) == Fr(95, 64)
d['(c\') 95a/64 > a/128+1 for a>=1024'] = Fr(95 * 1024, 64) > Fr(1024, 128) + 1 and Fr(95, 64) > Fr(1, 128)
d['(c\'\') n-3a<=a/64 => n-a <= 129a/64'] = (2 + Fr(1, 64)) == Fr(129, 64)
# (d) (5.1a) branch bounds
N = sp.symbols('N', positive=True)
target = (2 * N + 1) ** 2 / 24 - N ** 2 / 40
g1 = sp.expand(target - (4 * N + 1) ** 2 / 120)
g2 = sp.expand(target - N * (N - 1) / 12)
d['(d) sympy: target-(4n+1)^2/120 = ' + str(g1)] = all(c >= 0 for c in sp.Poly(g1, N).all_coeffs())
d['(d) sympy: target-n(n-1)/12 = ' + str(g2)] = all(c >= 0 for c in sp.Poly(g2, N).all_coeffs())
viol = []
maxmid = {}
for n_i in range(9, 1501):
    tgt = Fr((2 * n_i + 1) ** 2, 24) - Fr(n_i * n_i, 40)
    for r in range(4, n_i):
        a0, b0 = C2(r), r * (n_i - r)
        if a0 <= b0 <= 2 * a0:
            v = Fr(2 * b0 - a0, 3)
            if not (v <= Fr((4 * n_i + 1) ** 2, 120) and v < tgt):
                viol.append(('mid', n_i, r))
            maxmid[n_i] = max(maxmid.get(n_i, 0), v)
        if b0 <= a0:
            v = Fr(a0 + b0, 6)
            if not (v <= Fr(n_i * (n_i - 1), 12) and v < tgt):
                viol.append(('third', n_i, r))
    if n_i >= 100:
        if not (3 * n_i < tgt and Fr(n_i * (n_i - 1), 12) < tgt):
            viol.append(('small-r/empty', n_i))
d['(d) exhaustive integer branch check n=9..1500 violations=0'] = (len(viol) == 0)
# delta_C <= n^2/40 for n>=9 (used in text) : (1e-16+6e-12)n^2+n/6+1/24 <= n^2/40
d['(e) delta_C<=n^2/40 for all n>=9 (exact, n=9..10^4 and leading coeff)'] = all((Fr(1, 10 ** 16) + 6 * Fr(1, 10 ** 12)) * k * k + Fr(k, 6) + Fr(1, 24) <= Fr(k * k, 40) for k in range(9, 10001))
# delta_C <= (61/10) eps0 n^2 for n >= 4e12
nn0 = 4 * 10 ** 12
d['(f) delta_C<=(61/10)eps0 n^2 at n=4e12 (and hence above: n/6+1/24 <= (1e-13-1e-16)n^2 monotone)'] = ((Fr(1, 10 ** 16) + 6 * eps0) * nn0 ** 2 + Fr(nn0, 6) + Fr(1, 24) <= Fr(61, 10) * eps0 * nn0 ** 2)
# (g) r within 3e-6 n of n/3, a>=33n/100, |n-3a|<=a/64  (z3 LRA with sqrt bound pre-squared)
r_, n_z, a_z, u_z = z3.Reals('r nz az uz')
premg = [n_z >= 4 * 10 ** 12, (6 * r_ - 2 * n_z - 1) <= z3.Q(1211, 10 ** 8) * n_z, -(6 * r_ - 2 * n_z - 1) <= z3.Q(1211, 10 ** 8) * n_z]
# (6r-2n-1)^2 <= 24*6.1e-12 n^2 = 1.464e-10 n^2 ; sqrt(1.464e-10)=1.20996e-5 <= 1.211e-5
sq_ok = Fr(1211, 10 ** 8) ** 2 >= 24 * Fr(61, 10) * eps0
d['(g0) sqrt(24*6.1e-12) <= 1.211e-5'] = sq_ok
d['(g1) |r-n/3| < 3e-6 n'] = z3_unsat(premg, z3.Or(r_ - n_z / 3 >= z3.Q(3, 10 ** 6) * n_z, n_z / 3 - r_ >= z3.Q(3, 10 ** 6) * n_z))[0] == 'unsat'
premh = [n_z >= 4 * 10 ** 12, r_ - n_z / 3 <= z3.Q(3, 10 ** 6) * n_z, n_z / 3 - r_ <= z3.Q(3, 10 ** 6) * n_z, u_z >= 0, u_z <= z3.Q(3, 2 * 10 ** 6) * n_z, a_z == r_ - u_z]
d['(g2) a>=33n/100'] = z3_unsat(premh, a_z < z3.Q(33, 100) * n_z)[0] == 'unsat'
d['(g3) |n-3a|<=a/64'] = z3_unsat(premh, z3.Or(n_z - 3 * a_z > a_z / 64, 3 * a_z - n_z > a_z / 64))[0] == 'unsat'
ok = all(d.values())
negA = (Fr(1, 10 ** 12) + Fr(17, 10 ** 7)) <= Fr(33, 100) ** 2 / 65536
negD = all(maxmid[k] <= Fr(k * k, 8) - 1 for k in maxmid)
rec('T06', claim='(5.1)-(5.4) scalar steps: 1e-12+1.5e-6<=0.33^2/65536; u(u+1)/2<=eps0 n^2 => u<=3n/2e6; 7a/2-129a/64=95a/64; (5.1a) middle/third branch bounds below (2n+1)^2/24-n^2/40 for n>=9',
    manuscript_lines='456-514', method='exact Fractions, sympy polynomial coefficients, z3 (LRA/NRA), exhaustive integer branch scan n=9..1500',
    evidence_type='exact / symbolic (+ finite exhaustive scan for the branch bounds)', parameters={'branch_scan_n': [9, 1500]},
    details={k: bool(v) for k, v in d.items()} | {'branch_violations_first10': viol[:10]},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': '(a) with 1.7e-6 must fail; middle-branch max <= n^2/8-1 must fail somewhere (true max (n^2-1)/8 at r=(n+1)/2)',
                      '(a)_1.7e-6_accepted': negA, 'n^2/8-1_accepted': negD,
                      'result': 'PASS (rejected)' if not (negA or negD) else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T18
t0 = time.time()
x = sp.symbols('x', positive=True)  # x = s+1 >= 1
s_ = x - 1
coef = sp.expand(1 + 32 * s_ + 800 * (3 + 32 * s_) * x ** 2)
gap = sp.expand(38000 * x ** 3 - coef)
# positivity for x>=1: substitute x=1+y, y>=0, all coefficients nonnegative
y = sp.symbols('y', nonnegative=True)
gap_y = sp.Poly(sp.expand(gap.subs(x, 1 + y)), y).all_coeffs()
gapA = sp.Poly(sp.expand((2 * 10 ** 41 * x ** 8 - 40000 * x ** 3).subs(x, 1 + y)), y).all_coeffs()
epsS = 1 / (10 ** 41 * x ** 8)
maxeq = sp.simplify(2 / epsS - 2 * 10 ** 41 * x ** 8) == 0
# total: max a+m+K R* s.t. a + m/(2000 x^2) + R* <= delta  -> max(1, 2000x^2, K) ; show each <= 40000 x^3
tot1 = sp.Poly(sp.expand((40000 * x ** 3 - 2000 * x ** 2).subs(x, 1 + y)), y).all_coeffs()
# chain (6.14) via z3 for s=0..60 (linear once s fixed)
chain_ok = True
for s in range(0, 61):
    aa, mm, EE, rn, ntW, Rs, dE, dl = z3.Reals('aa mm EE rn ntW Rs dE dl')
    K = 1 + 32 * s + 800 * (3 + 32 * s) * (s + 1) ** 2
    prem = [aa >= 0, mm >= 0, EE >= 0, rn >= 0, ntW >= 0, Rs >= 0,
            aa + mm / (2000 * (s + 1) ** 2) + Rs <= dl, ntW <= 800 * (s + 1) ** 2 * Rs, EE <= Rs + ntW, rn <= 16 * s * EE,
            dE <= aa + mm + EE + 2 * rn + 2 * ntW]
    if z3_unsat(prem, dE > aa + mm + K * Rs)[0] != 'unsat' or z3_unsat(prem, dE > 40000 * (s + 1) ** 3 * dl)[0] != 'unsat':
        chain_ok = False
# C' partition constants: (1+4A)+3A = 1+7A ; 10x
Aa = sp.symbols('A_s')
c_ok = sp.expand((1 + 4 * Aa) + 3 * Aa - (1 + 7 * Aa)) == 0
ok = all(c >= 0 for c in gap_y) and all(c >= 0 for c in gapA) and maxeq and all(c >= 0 for c in tot1) and chain_ok and c_ok
neg_coef = sp.Poly(sp.expand((25000 * x ** 3 - coef)), x).all_coeffs()
neg_ok = sp.Poly(coef, x).LC() > 25000  # leading coefficient 25600 > 25000 so the bound 25000(s+1)^3 fails for large s
neg_val = [(s, (1 + 32 * s + 800 * (3 + 32 * s) * (s + 1) ** 2) <= 25000 * (s + 1) ** 3) for s in (0, 10, 100, 1000)]
rec('T18', claim="Thm C' constants: max{40000(s+1)^3, 2/eps_s} = 2e41(s+1)^8; 1+32s+800(3+32s)(s+1)^2 <= 38000(s+1)^3; d_E<=40000(s+1)^3 delta; 1+7A_s",
    manuscript_lines='101-107, 910-965, 2107-2118', method='sympy polynomial with nonnegative coefficients after x=1+y; z3 LRA for the (6.14) chain for each s=0..60',
    evidence_type='exact / symbolic', parameters={'z3_chain_s': [0, 60]},
    details={'coef_poly_in_x=s+1': str(coef), '38000x^3-coef in y=x-1 coeffs': [str(c) for c in gap_y], 'max_equals_2/eps_s': maxeq, 'chain_z3_ok_s0..60': chain_ok, '1+7A identity': c_ok},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': 'corrupted coefficient bound 25000(s+1)^3 must fail for large s (leading coefficient 25600)', 'values(s, holds)': neg_val,
                      'result': 'PASS (rejected)' if neg_ok and not neg_val[-1][1] else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T19
t0 = time.time()
g0, ep, N0, t, dl, dlc = z3.Reals('g0 ep N0 t dl dlc')
base = [ep > 0, g0 > 0, N0 >= 0, t >= N0, dl >= 0, dl <= g0 * t * (t - N0), dlc <= dl - ep * t + z3.Q(1, 3)]
prem19 = base + [g0 <= ep / 4, ep * N0 >= 1]
concl19 = dlc <= g0 * (t - 1) * (t - 1 - N0)
r19 = z3_unsat(prem19, z3.Not(concl19))[0]
# change of RHS: g0 t(t-N0) - g0 (t-1)(t-1-N0) = g0(2t-1-N0) <= ep t/2
r19b = z3_unsat([ep > 0, g0 > 0, N0 >= 0, t >= N0, g0 <= ep / 4], g0 * (2 * t - 1 - N0) > ep * t / 2)[0]
# bottom-order: t = N0 forces dl = 0 and dlc < 0
r19c = z3_unsat(prem19 + [t == N0], dlc >= 0)[0]
n1 = z3_unsat(base + [g0 <= ep, ep * N0 >= 1], z3.Not(concl19))[0]
n2 = z3_unsat(base + [g0 <= ep / 4], z3.Not(concl19))[0]
rec('T19', claim='F.1 deletion invariant 0<=delta<=g0 t(t-N0), g0<=eps/4, eps N0>=1, delta\'<=delta-eps t+1/3 => delta\'<=g0(t-1)(t-1-N0); bottom order contradiction',
    manuscript_lines='2141-2146 (with 973-977)', method='z3 nonlinear real arithmetic (nlsat); premises AND NOT(conclusion) unsat', evidence_type='exact (decision procedure, NRA)',
    parameters={}, details={'invariant_preserved': r19, 'rhs_change_le_eps_t/2': r19b, 't=N0_forces_negative_child_deficit': r19c},
    result='PASS' if (r19 == 'unsat' and r19b == 'unsat' and r19c == 'unsat') else ('INCONCLUSIVE' if 'unknown' in (r19, r19b, r19c) else 'FAIL'),
    negative_control={'description': 'with g0<=eps (not eps/4), or without eps N0>=1, the invariant must be refutable (sat)', 'g0<=eps': n1, 'no_epsN0>=1': n2,
                      'result': 'PASS (rejected)' if (n1 == 'sat' and n2 == 'sat') else ('INCONCLUSIVE' if 'unknown' in (n1, n2) else 'FAIL (accepted)')},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T21 (symbolic part)
t0 = time.time()
gain = {r: C2(r) - 1 for r in (2, 3, 4)}
tab1 = gain == {2: 0, 3: 2, 4: 5} and all(C2(r) - gain[r] == 1 for r in (2, 3, 4))
ratio = max(Fr(gain[r], C2(r)) for r in (3, 4)) == Fr(5, 6)
eG, gP, Wst, Mn = sp.symbols('e g W Mn')
eq13 = sp.simplify((eG - gP - Mn) - ((Wst - gP) - (Mn - (eG - Wst)))) == 0
rec('T21', claim='Table 1 gains; Lemma 2.1 |Q|=e-g(P); (1.3) equivalence; (1.3a) g(Q)+|Q|=e; (2.4) w<=5/6 e', manuscript_lines='113-138, 196-238',
    method='symbolic identities here; (1.3a)/(2.1) on random partitions and (2.4) on all exact W* values are in t_graphs.py (T21b)',
    evidence_type='exact / symbolic', parameters={},
    details={'table1': tab1, 'max gain/edges = 5/6': ratio, '(1.3) difference identity': eq13},
    result='PASS' if (tab1 and ratio and eq13) else 'FAIL', negative_control={'description': 'none predeclared (trivial)', 'result': 'N/A'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T22
t0 = time.time()
verts = [(Fr(1), Fr(0), Fr(0)), (Fr(0), Fr(16), Fr(0)), (Fr(0), Fr(0), Fr(2))]  # (r,m,A) vertices of r+m/16+A/2<=1, >=0 (plus origin)
val48 = max(r + A + 3 * m for r, m, A in verts)
val16 = max(m + A for r, m, A in verts)
val_edges = 10 * val48
# cross-check with HiGHS
from scipy.optimize import linprog
lp = linprog([-1, -3, -1], A_ub=[[1, 1 / 16, 1 / 2]], b_ub=[1], bounds=(0, None), method='highs')
ok = (val48 == 48 and val16 == 16 and val_edges == 480 and abs(-lp.fun - 48) < 1e-9)
rec('T22', claim='Thm 6.1/Cor 6.1a: from (6.7) r+m/16+A/2<=delta (r,m,A>=0): r+A+3m<=48delta (optimal), m+A<=16delta, edges 10tau+480delta',
    manuscript_lines='837-877', method='exact LP by vertex enumeration of the simplex r+m/16+A/2<=1; HiGHS cross-check', evidence_type='exact',
    parameters={}, details={'max r+A+3m': str(val48), 'max m+A': str(val16), 'argmax': '(r,m,A)=(0,16,0)', 'highs': -lp.fun},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': 'constant 47 must fail (vertex m=16delta gives 48delta)', 'accepted_by_test': val48 <= 47,
                      'result': 'PASS (rejected)' if not val48 <= 47 else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

# ------------------------------------------------------------------ T24
t0 = time.time()
NMAX = 10 ** 5
a1 = all(6 * M(k) >= k * (k + 1) - 6 for k in range(NMAX + 1))
a2 = all(((2 * k + 1) ** 2) // 24 == M(k) for k in range(NMAX + 1))
a3 = all(6 * M(k) >= k * k for k in range(6, NMAX + 1))
a4 = all(k * k <= 2 ** k for k in range(4, 2001))
Nn = sp.symbols('N')
# (N+1)^2<=2N^2 for N>=3: substitute N=3+y (here written Nn+3), coefficients >= 0
a5 = all(c >= 0 for c in sp.Poly(sp.expand(2 * (Nn + 3) ** 2 - (Nn + 4) ** 2), Nn).all_coeffs())
a6 = all(6 * M(k) <= k * k + k for k in range(NMAX + 1))
rem = sorted(set((k * (k + 1)) % 6 for k in range(NMAX + 1)))
ok = a1 and a2 and a3 and a4 and a5 and a6
negN = 3 * 3 <= 2 ** 3
negM = all(12 * M(k) >= 2 * k * (k + 1) - 3 for k in range(NMAX + 1))  # M >= n(n+1)/6 - 1/4 : must fail
rec('T24', claim='(6.5a)/(6.5): M(n)>=n(n+1)/6-1; M(n)<=n^2/6+n/6; M(n)>=n^2/6 (n>=6, Cor 3.5); floor((2n+1)^2/24)=M(n) (§2.3); N^2<=2^N for N>=4 (§6.3)',
    manuscript_lines='250, 301, 779-809', method='exhaustive exact integers n<=1e5, N<=2000; sympy induction step (N+1)^2<=2N^2 for N>=3', evidence_type='exact (finite exhaustive + symbolic induction step)',
    parameters={'n_max': NMAX, 'N_max': 2000}, details={'M>=n(n+1)/6-1': a1, 'floor((2n+1)^2/24)=M': a2, 'M>=n^2/6 (n>=6)': a3, 'N^2<=2^N (4..2000)': a4,
                                                        'induction step coefficients >=0': a5, 'M<=n^2/6+n/6': a6, 'n(n+1) mod 6 values': rem},
    result='PASS' if ok else 'FAIL',
    negative_control={'description': 'N=3 must violate N^2<=2^N; M(n)>=n(n+1)/6-1/4 must fail (remainder 2/6)', 'N=3_accepted': negN, 'quarter_accepted': negM,
                      'result': 'PASS (rejected)' if not (negN or negM) else 'FAIL (accepted)'},
    runtime_s=round(time.time() - t0, 3))

dump('scalar_tests.json', OUT)
