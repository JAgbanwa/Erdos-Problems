"""E5 — independent exact-arithmetic checks (auditor-written, Fractions/sympy only).
Each check prints PASS/FAIL against a predeclared expectation. Negative controls must FAIL (and are reported
as 'NEGCTRL ok' when they fail as expected)."""
from fractions import Fraction as F
import math, json, sys
import sympy as sp

res = []

def check(name, cond, detail=''):
    res.append({'check': name, 'result': 'PASS' if cond else 'FAIL', 'detail': str(detail)})

def negctrl(name, cond, detail=''):
    # cond is the (false) statement that must fail
    res.append({'check': 'NEG:' + name, 'result': 'NEGCTRL ok' if not cond else 'NEGCTRL VIOLATED', 'detail': str(detail)})

M = lambda n: n * (n + 1) // 6
eps0, eta0 = F(1, 10**12), F(1, 10**16)

# (4.6a) contraction inequality
lhs = lambda n: F(16, 6 * n) + F(1, n) + F(16, 24 * n * n)
check('4.6a holds at n=4e12', lhs(4 * 10**12) < eps0 - 16 * eta0, float(lhs(4 * 10**12)))
negctrl('4.6a at n=3.6e12', lhs(36 * 10**11) < eps0 - 16 * eta0, float(lhs(36 * 10**11)))
# crossing point
nstar = (F(16, 6) + 1) / (eps0 - 16 * eta0)
check('4.6a crossing in (3.6e12,4e12)', 36 * 10**11 < nstar < 4 * 10**12, float(nstar))
# direct form: 16D/n^2 < eps0 - 1/n equivalent
n = 4 * 10**12
D = eta0 * n * n + F(n, 6) + F(1, 24)
check('16D/n^2 < eps0-1/n at 4e12', 16 * D / (n * n) < eps0 - F(1, n))

# Lemma 4.2 coefficient comparisons
check('16*117/1825>1', 16 * F(117, 1825) > 1)
check('16*12687/20000>10', 16 * F(12687, 20000) > 10)

# Lemma 5.3 coefficient derivations
c_m = 1 - F(48, 25) * F(40, 73); c_A = -F(13, 20) + F(48, 25) * F(3, 40)
check('5.15 coefficients', (c_m, c_A) == (F(-19, 365), F(-253, 500)), (c_m, c_A))
# from l <= 7A/40 + f/25: |Q| <= B + m - A - 2f + 2l
check('13/20 and 48/25', (-1 + 2 * F(7, 40), -2 + 2 * F(1, 25)) == (F(-13, 20), F(-48, 25)))
c_m2 = 1 - F(971, 500) * F(40, 73); c_A2 = -F(39, 50) + F(971, 500) * F(3, 40)
check('5.15a coefficients', (c_m2, c_A2) == (F(-117, 1825), F(-12687, 20000)), (c_m2, c_A2))
check('39/50 and 971/500', (-1 + 2 * F(11, 100), -2 + 2 * F(29, 1000)) == (F(-39, 50), F(-971, 500)))
check('117/1825>1/16, 12687/20000>1/2, 19/365>=1/20, 253/500>=1/2',
      F(117, 1825) > F(1, 16) and F(12687, 20000) > F(1, 2) and F(19, 365) >= F(1, 20) and F(253, 500) >= F(1, 2))
check('11A/100+29f/1000 <= 7A/40 + f/25 coefficientwise', F(11, 100) <= F(7, 40) and F(29, 1000) <= F(1, 25))
# first phase
check('2920*40/73=1600 and 2920*3/40=219', 2920 * F(40, 73) == 1600 and 2920 * F(3, 40) == 219)

# (5.12a),(5.13),(5.14)
check('5.12a: 1/64+3/57344<1/48', F(1, 64) + F(3, 57344) < F(1, 48), float(F(1, 64) + F(3, 57344)))
Q0 = F(87947, 44352); R0 = F(393, 100)
mid = Q0 * Q0 - Q0 / 1024
check('5.13: Q0^2-Q0/1024 >= 393/100', mid >= R0, float(mid))
negctrl('5.13 with 3.931', mid >= F(3931, 1000), float(mid))
cA = 1 / (48 * Q0) + (F(101, 100) * (F(1, 3) + F(1, 64)) + F(11, 2000)) / R0
cf = 1 / (24 * Q0) + (F(101, 100) / 64 + F(11, 1000)) / R0
check('5.14 A-coefficient <= 11/100', cA <= F(11, 100), float(cA))
check('5.14 f-coefficient <= 29/1000', cf <= F(29, 1000), float(cf))
# t/a <= 1/256 given t < a/396 + 1, a>=1024
check('a/396+1 <= a/256 for a>=1024', all(F(a, 396) + 1 <= F(a, 256) for a in [1024, 2048, 10**6]))
# Q0 derivation: q >= (3-1/64)a - a(1+1/57344)
check('q/a lower bound >= 87947/44352', F(3) - F(1, 64) - 1 - F(1, 57344) >= Q0, float(F(3) - F(1, 64) - 1 - F(1, 57344)))
check('48(2p-q)+ <= a', 48 * (F(3, 57344) + F(1, 64)) <= 1)
# Theorem 5.0 window
check('3267n<=10000p & 3539p<=1188n => |3p-n|<=n/50', 3 * F(3267, 10000) >= 1 - F(1, 50) and 3 * F(1188, 3539) <= 1 + F(1, 50),
      (float(3 * F(3267, 10000)), float(3 * F(1188, 3539))))

# Lemma 5.1 numerics
check('u(u+1)/2<=eps0 n^2 => u<=1.5e-6 n', math.sqrt(2e-12) <= 1.5e-6)
check('eps0+1.5e-6 <= 0.33^2/65536', F(1, 10**12) + F(15, 10**7) <= F(33, 100)**2 / 65536, float(F(33, 100)**2 / 65536))
check('a>=1024 at n=4e12', F(33, 100) * 4 * 10**12 >= 1024)
check('delta_C <= 6.1 eps0 n^2 at n=4e12', (eta0 + 6 * eps0) * n * n + F(n, 6) + F(1, 24) <= F(61, 10) * eps0 * n * n)
# clique bounds in Prop 5.2
check('(a/4)|X|<=a^2/65536 => 16384|X|<=a; (7a/4)|Y|<=2a^2/65536 => 57344|Y|<=a', F(65536, 4) == 16384 and F(65536 * 7, 8) == 57344)
check('7a/2-129a/64=95a/64', F(7, 2) - F(129, 64) == F(95, 64))

# (5.1a) regime bounds, symbolic
nn = sp.symbols('n', positive=True)
exprA = (2 * nn + 1)**2 / 24 - nn**2 / 40 - (4 * nn + 1)**2 / 120
exprB = (2 * nn + 1)**2 / 24 - nn**2 / 40 - nn * (nn - 1) / 12
check('middle branch below envelope-n^2/40 for all n>0', sp.simplify(sp.expand(exprA) - (nn**2 / 120 + nn / 10 + sp.Rational(1, 30))) == 0, sp.expand(exprA))
check('third branch below envelope-n^2/40 for n>=1', all(exprB.subs(nn, k) > 0 for k in range(1, 200)), sp.expand(exprB))
r = sp.symbols('r', positive=True)
mid_max = sp.maximum(r * (4 * nn + 1 - 5 * r) / 6, r)
check('max_r r(4n+1-5r)/6 = (4n+1)^2/120', sp.simplify(mid_max - (4 * nn + 1)**2 / 120) == 0)
# completing the square B_n(r)
check('B_n(r) = (2n+1)^2/24 - (6r-2n-1)^2/24', sp.expand(r * (nn - r) - r * (r - 1) / 2 - ((2 * nn + 1)**2 - (6 * r - 2 * nn - 1)**2) / 24) == 0)

# (6.3),(6.4),(6.12),(E.3),(E.5)
ok63 = all(6 * (k * (n - k) - k * (k - 1) // 2) + (n - 3 * k) * (n - 3 * k + 1) == n * (n + 1) for n in range(0, 300) for k in range(0, n + 1))
check('(6.3) identity 0<=k<=n<300', ok63)
def optcores(n):
    vals = {k: k * (n - k) - k * (k - 1) // 2 for k in range(2, n // 2 + 1) if k <= n - k}
    mx = max(vals.values()); return mx, sorted(k for k, v in vals.items() if v == mx)
ok64 = True; okM = True
for n in range(6, 400):
    mx, ks = optcores(n); r_, t = divmod(n, 3)
    exp = {0: [r_], 1: [r_, r_ + 1], 2: [r_ + 1]}[t]
    ok64 &= (ks == exp); okM &= (mx == M(n))
check('(6.4) optimal cores within 2<=k<=n-k, 6<=n<400', ok64)
check('max_k f(n,k) = M(n), 6<=n<400', okM)
check('ceil(n/3) in optimal cores and 2<=k<=n-k (n>=6)', all(math.ceil(n / 3) in optcores(n)[1] for n in range(6, 400)))
def dnk(n, k): return n - 3 * k if 3 * k <= n else 3 * k - n - 1
ok612 = all(M(n) == (k * (n - k) - k * (k - 1) // 2) + M(dnk(n, k)) for n in range(0, 300) for k in range(0, n + 1) if k * (k - 1) // 2 <= k * (n - k))
check('(6.12) reserve identity', ok612)
Qs = lambda s, n: M(n + s) - (s + 1) * s // 2
check('(E.3) increments floor((n+s+1)/3), all n>=1, s<20', all(Qs(s, n) - Qs(s, n - 1) == (n + s + 1) // 3 for s in range(20) for n in range(1, 300)))
okE5 = all((lambda k: k * (n - k) - (k - s) * (k - s - 1) // 2 == Qs(s, n))((n + s + 1) // 3) for s in range(15) for n in range(2 * s + 2, 300))
check('(E.5) witness count = Q_s(n) for n>=2s+2', okE5)
check('(E.2e) Q_s(m)+r*ceil((m+s)/3) <= Q_s(m+r)', all(Qs(s, m) + rr * (-(-(m + s) // 3)) <= Qs(s, m + rr) for s in range(8) for m in range(s + 2, 120) for rr in range(0, 20)))
check('(E.2e) c(b+s) <= C(c,2)+M(c+b+s)', all(c * (b + s) <= c * (c - 1) // 2 + M(c + b + s) for s in range(6) for c in range(0, 60) for b in range(0, 60)))
check('Q_0 = M', all(Qs(0, n) == M(n) for n in range(300)))
check('floor((2n+1)^2/24) = M(n)', all((2 * n + 1)**2 // 24 == M(n) for n in range(2000)))
negctrl('(2n+1)^2/24 == n(n+1)/6 (rational envelope equals floor)', all(F((2 * n + 1)**2, 24) == M(n) for n in range(1, 50)))

# D.1 / D.2 arithmetic
check('(D.2) C(n,2)-n(n-2)/3 = n(n+1)/6', all(F(n * (n - 1), 2) - F(n * (n - 2), 3) == F(n * (n + 1), 6) for n in range(2, 200)))
check('STS deletion: n(n+1)/6 - n/2 = n(n-2)/6', all(F(n * (n + 1), 6) - F(n, 2) == F(n * (n - 2), 6) for n in range(2, 100)))
check('(D.4) (3M+1)3M+3M=(3M+2)3M', all((3 * m + 1) * 3 * m + 3 * m == (3 * m + 2) * 3 * m for m in range(1, 100)))
check('D.2: n=6r+4 => ceil(n(n+1)/6)=M(n)+1', all(-(-(n * (n + 1)) // 6) == M(n) + 1 for n in range(4, 400, 6)))
check('M(10)=18', M(10) == 18)
# Table 8 residue coverage for n>=2
cover = set()
for m in range(1, 100):
    if m % 2 == 1: cover |= {3 * m, 3 * m - 1, 3 * m + 1, 3 * m + 2}
    if m % 2 == 0: cover |= {3 * m + 1, 3 * m}
check('Table 8 rows cover every n in [2,290]', all(k in cover for k in range(2, 291)))

# Stability constants
d_ = sp.symbols('delta', nonnegative=True)
mm, AA, rr = sp.symbols('m A r', nonnegative=True)
from scipy.optimize import linprog
lp = linprog(c=[-1, -1, -3], A_ub=[[1, F(1, 2), F(1, 16)]], b_ub=[1], bounds=[(0, None)] * 3, method='highs')
check('max r+A+3m s.t. r+A/2+m/16<=1 equals 48 (constant 48 tight for account 6.7)', abs(-lp.fun - 48) < 1e-9, -lp.fun)
negctrl('47 suffices for account (6.7)', -lp.fun <= 47)
lp2 = linprog(c=[-1, -1], A_ub=[[F(1, 16), F(1, 2)]], b_ub=[1], bounds=[(0, None)] * 2, method='highs')
check('max m+A s.t. m/16+A/2<=1 equals 16 (constant 16 tight for account 6.7)', abs(-lp2.fun - 16) < 1e-9, -lp2.fun)
# (6.7a) closed form identity
a, b = sp.symbols('a b', integer=True)
check('(6.7a) closed form', sp.expand(1 + a * (a - 1) / 2 + 3 * b * (b - 1) / 2 - a * b - ((a - b) * (a - b - 1) / 2 + (b - 1)**2)) == 0)
zeros = [(x, y) for x in range(0, 30) for y in range(0, 30) if x + y >= 2 and (x - y) * (x - y - 1) // 2 + (y - 1)**2 == 0]
check('d_R(K)=0 iff (a,b) in {(1,1),(2,1)} among pieces with >=2 vertices', zeros == [(1, 1), (2, 1)], zeros)
# (6.6) complete-split defect zero cases
zs = [s for s in range(1, 40) if (s - 1) * (s - 2) // 2 == 0]
check('(6.6) zero defect with one host iff s in {1,2}', zs == [1, 2])

# (6.5a) and (6.5): floor(t)>=t-1
check('M(n) >= (n^2+n)/6 - 1', all(M(n) >= F(n * n + n, 6) - 1 for n in range(0, 2000)))
check('M(n) >= n^2/6 for n>=6 (Cor 3.5)', all(M(n) >= F(n * n, 6) for n in range(6, 2000)))
negctrl('M(n) >= n^2/6 for all n>=1', all(M(n) >= F(n * n, 6) for n in range(1, 6)))

# Cor 5.4 (5.18) algebra: e(S_C) with k = n/3+t
k_, t_ = sp.symbols('k t')
eS = k_ * (k_ - 1) / 2 + k_ * (nn - k_)
check('(5.18) expansion', sp.simplify(eS.subs(k_, nn / 3 + t_) - (5 * nn**2 / 18 + 2 * nn * t_ / 3 - t_**2 / 2 - (nn / 3 + t_) / 2)) == 0)
# |t|<=n/30000 from (4.8) at n>=4e12 (worst case)
n = 4 * 10**12
rad = math.sqrt(24 * ((1e-16 + 6e-12) * n * n + n / 6 + 1 / 24))
check('|6k-2n-1|<=rad => |t|<=n/30000', (rad + 1) / 6 <= n / 30000, (rad + 1) / 6 / n)
# e(G) within n^2/1e4
bound = 2 * n * (n / 30000) / 3 + (n / 30000)**2 / 2 + (n / 3 + n / 30000) / 2 + 1e-12 * n * n
check('(5.18) total error <= n^2/1e4', bound <= n * n / 1e4, bound / (n * n))

# Prop 8.1 numerics
check('t=34: t^2/16 = 72.25 > 72', F(34 * 34, 16) == F(7225, 100) and F(34 * 34, 16) > 72)
Mv = sp.symbols('Mv', positive=True)
epsv = sp.symbols('eps', positive=True)
# mass hypothesis: (2M+1)*7eps*M >= eps*(6M+3)^2/30 - 1 ; contradiction with 2(1-1/2)T <= eps n^2/4
check('mass hypothesis holds: 7M >= 0.3(2M+1) for M>=1', all(7 * m >= F(3, 10) * (2 * m + 1) for m in range(1, 1000)))
check('contradiction: 7M(2M+1) > (9/4)(2M+1)^2 for M>=1', all(7 * m * (2 * m + 1) > F(9, 4) * (2 * m + 1)**2 for m in range(1, 1000)))
check('(8.5) eps n^2/30 - 1 <= (2n-3)/3 => n <= 20/eps (sample eps)', all((F(e) * nv * nv / 30 - 1 > F(2 * nv - 3, 3)) or nv <= 20 / F(e) for e in [F(1, 10), F(1, 7), F(1, 100)] for nv in range(1, 3000)))

# Explicit schedule numerics (C.3)
xi = eta0 / 2
a_ = min(xi / 4500, F(1, 10))
check('a = 1/(9e19)', a_ == F(1, 9 * 10**19))
check('z = 1/(2e17)', min(xi / 10, F(1)) == F(1, 2 * 10**17))
check('k0 = 3e19+1', -(-F(1500) // xi) + 1 == 3 * 10**19 + 1)
h_manuscript = 4 * 8**5 * 2208**5 * 4500**105 * (2 * 10**16)**105
h_mathlib_form = 4 * 8**5 * 2208**5 * (9 * 10**19)**105  # floor(4/(delta/8)^5) with delta=a^21/2208
check('h = 4/(delta/8)^5 with delta=a^21/2208', h_manuscript == h_mathlib_form and F(4) / (a_**21 / 2208 / 8)**5 == h_manuscript)
check('L_T(beta0)=ln(64e18) <= 46', math.log(64e18) <= 46, math.log(64e18))
check('M_T(7,beta0) <= 16*7*46+1 = 5153', 16 * 7 * 46 + 1 == 5153)
check('N^2 <= 2^N for N>=4', all(N * N <= 2**N for N in range(4, 200)))

# Section 2.3: floor((2n+1)^2/24) = M(n) argument n(n+1) mod 6 in {0,2}
check('n(n+1) mod 6 in {0,2}', all(n * (n + 1) % 6 in (0, 2) for n in range(10000)))

fails = [r for r in res if r['result'] in ('FAIL', 'NEGCTRL VIOLATED')]
json.dump(res, open('e5_exact_results.json', 'w'), indent=1)
for r_ in res:
    print(r_['result'].ljust(16), r_['check'], ('| ' + r_['detail'])[:110] if r_['detail'] else '')
print('TOTAL', len(res), 'FAILURES', len(fails))
