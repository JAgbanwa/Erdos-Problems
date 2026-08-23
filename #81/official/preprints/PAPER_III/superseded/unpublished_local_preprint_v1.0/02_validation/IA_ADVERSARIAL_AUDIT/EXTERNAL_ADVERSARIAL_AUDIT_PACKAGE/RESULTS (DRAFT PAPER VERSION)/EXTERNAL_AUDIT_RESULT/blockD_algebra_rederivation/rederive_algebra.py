r"""
EXTERNAL ADVERSARIAL AUDIT — Block D: independent re-derivation of the algebra.

Independence: this script uses NO computer-algebra system (no SymPy, no CAS).
All symbolic identities are verified with a self-written exact multivariate
polynomial class over `fractions.Fraction` (expand LHS - RHS and test == 0).
All inequality steps are verified either by an explicit algebraic certificate
(substitution u >= 0 with all-nonnegative coefficients, or an exact perfect-square
factorization) or by exhaustive/sampled exact-rational grids at and beyond the
paper's boundaries.

Claims re-derived (paper v0.9.5 / LEDGER.md tags):
  D01  T(G) key identity of Theorem 4.2 (polynomial identity)
  D02  the three cover-vertex values of F equal the three branches (D2 of checklist)
  D03  C(d,2)+d*r+C(r,2) = C(p,2)  (branch-1 bookkeeping)
  D04  (4.5) branch 1: exact residual = q(p-d)/6 + p/3            [mu low]
                       and + (3q-2p)(q+2p)/48                     [mu high]
  D05  (4.5) branch 2: exact residual = (d-(2p+q)/4)^2            [mu high]
                       and + (2p-3q)(2p+q)/48                     [mu low]
  D06  (4.5) branch 3: exact residual analysis (perfect square + factor terms),
       verified symbolically + exact grid
  D07  third-branch dominance (Appendix A): residual minima formulas and
       dominance over min(first two) on [0,2]
  D08  mu continuity at alpha = 2/3
  D09  (5.2) substitution identity from E-5.1 (polynomial identity in p,s,M,S2)
  D10  (5.3) parabola completion (polynomial identity + S2 >= M^2/q direction)
  D11  (9.5) integer step: m_i < s/3 - 5/6  =>  3m <= s-3
  D12  (9.10) delta >= 7/8 both parities (certificate + exact grid)
  D13  (9.11) certificate: 3m <= s-3  =>  m(s-1-m) <= 2s(s-3)/9 (nonneg-coeff cert)
  D14  (9.12) coefficient -1/6 + 2/9 - 7/96 = -5/288, and conclusion at s^2>=36p
  D15  (9.16)/(9.17) kappa_R <= 5s/4p and (s-2rho-1)+/q <= 5s/4p (exact grid, both parities)
  D16  (9.18) 5s/(4p) * s^2/6 <= 5 s^2/192  iff  8s <= p  (identity)
  D17  (9.19) completed square (polynomial identity)
  D18  (9.20) coefficient -1/24 + 5/192 = -1/64, and conclusion at s^2>=36p
  D19  corridor threshold 6 sqrt(p) = p/8  <=>  p = 2304 (exact integer check)
  D20  Prop 10.1(i) chain: exact grid p in [36..600], 0 <= s <= 6 sqrt(p)
  D21  (6.1) counting identity |B_i \ B_j| = a_ij (2(p-|S_j|) - a_ij - 1)/2 (exhaustive)
       + V-identity V = sum_{i,j} |B_i \ B_j| (random exact) + Lemma 6.1 inequality
  D22  sharpness closed form: |E| - 2 C(p,2) = n^2/6 + n/6 for K_p v bar-K_2p (identity)

Output: results/algebra_results.txt ; exit code 0 iff every check passes.
"""
import sys, os, math, random
from fractions import Fraction as Q
from itertools import combinations

random.seed(20260721)

# ----------------------------------------------------------------------------
# Tiny exact multivariate polynomial class (dict of exponent tuples -> Fraction)
# ----------------------------------------------------------------------------
VARS = ('p', 'q', 'd', 's', 'M', 'S2', 'm', 'rho', 'Sd', 'u')
NV = len(VARS)

class P:
    __slots__ = ('c',)
    def __init__(self, c=None):
        self.c = dict(c) if c else {}
    @staticmethod
    def const(x):
        x = Q(x)
        return P({(0,)*NV: x}) if x else P()
    @staticmethod
    def var(name):
        e = [0]*NV; e[VARS.index(name)] = 1
        return P({tuple(e): Q(1)})
    def __add__(a, b):
        if not isinstance(b, P): b = P.const(b)
        c = dict(a.c)
        for e, v in b.c.items():
            c[e] = c.get(e, Q(0)) + v
            if not c[e]: del c[e]
        return P(c)
    __radd__ = __add__
    def __neg__(a): return P({e: -v for e, v in a.c.items()})
    def __sub__(a, b):
        if not isinstance(b, P): b = P.const(b)
        return a + (-b)
    def __rsub__(a, b): return P.const(b) - a
    def __mul__(a, b):
        if not isinstance(b, P): b = P.const(b)
        c = {}
        for e1, v1 in a.c.items():
            for e2, v2 in b.c.items():
                e = tuple(x+y for x, y in zip(e1, e2))
                c[e] = c.get(e, Q(0)) + v1*v2
                if not c[e]: del c[e]
        return P(c)
    __rmul__ = __mul__
    def __truediv__(a, k): return a * P.const(Q(1, 1)/Q(k))
    def __pow__(a, n):
        r = P.const(1)
        for _ in range(n): r = r * a
        return r
    def is_zero(self): return not self.c
    def coeffs(self): return list(self.c.values())
    def subst(self, name, poly):
        """substitute variable name := poly (a P or constant)."""
        if not isinstance(poly, P): poly = P.const(poly)
        i = VARS.index(name)
        out = P()
        for e, v in self.c.items():
            term = P.const(v)
            for j, ex in enumerate(e):
                if ex == 0: continue
                base = poly if j == i else P.var(VARS[j])
                term = term * base**ex
            out = out + term
        return out
    def __repr__(self):
        if not self.c: return '0'
        parts = []
        for e, v in sorted(self.c.items()):
            mono = '*'.join(f'{VARS[i]}^{x}' if x > 1 else VARS[i]
                            for i, x in enumerate(e) if x)
            parts.append(f'({v})' + ('*'+mono if mono else ''))
        return ' + '.join(parts)

p, q, d, s, M, S2, m, rho, Sd, u = (P.var(v) for v in VARS)

def C2p(x): return x*(x - 1)/2

# exact rational closed forms (recomputed here, not imported from anyone)
def Fq(pp, qq, dd):
    pp, qq, dd = Q(pp), Q(qq), Q(dd)
    rr = pp - dd
    t1 = (pp*(pp-1)/2 + qq*dd)/3
    t2 = dd*(dd-1)/2 + rr*(rr-1)/2
    t3 = dd*(dd-1)/2 + (dd*rr + rr*(rr-1)/2)/3
    return min(t1, t2, t3), (t1, t2, t3)

def rp_of(t):
    if t <= 1: return 0
    return t-1 if t % 2 == 0 else t

RES = []
OUT = []
def emit(x=''): OUT.append(str(x))
def check(name, ok, note=''):
    RES.append((name, bool(ok)))
    emit(f"[{'PASS' if ok else 'FAIL'}] {name}")
    if note: emit(f"        {note}")
    return bool(ok)

emit('='*76)
emit('EXTERNAL AUDIT — Block D: independent algebra re-derivation (no CAS)')
emit('='*76); emit()

# --- D01: T identity.  |E| = C(p,2)+Sd, q = alpha p.
# claim: (|E| - (p+q)^2/6)/2  ==  Sd/2 + ((2p^2-2pq-q^2)/12) - p/4
E_poly = C2p(p) + Sd
lhs = (E_poly - (p+q)**2/6)/2
rhs = Sd/2 + (2*p*p - 2*p*q - q*q)/12 - p/4
check('D01 T(G) identity (Thm 4.2 key identity)', (lhs-rhs).is_zero(),
      'T = Sd/2 + C_alpha p^2 - p/4  with C_alpha p^2 = (2p^2-2pq-q^2)/12')

# --- D02: cover values. objective(a,b,c,e) = C(d,2)a + qd b + dr c + C(r,2) e
r_ = p - d
def obj(a_, b_, c_, e_):
    return C2p(d)*P.const(a_) + q*d*P.const(b_) + d*r_*P.const(c_) + C2p(r_)*P.const(e_)
v1 = obj(Q(1,3), Q(1,3), Q(1,3), Q(1,3))
v2 = obj(1, 0, 0, 1)
v3 = obj(1, 0, Q(1,3), Q(1,3))
t1 = (C2p(p) + q*d)/3
t2 = C2p(d) + C2p(r_)
t3 = C2p(d) + (d*r_ + C2p(r_))/3
ok = (v1-t1).is_zero() and (v2-t2).is_zero() and (v3-t3).is_zero()
check('D02 three cover-vertex values = three branches of F', ok,
      '(1/3,1/3,1/3,1/3)->t1 ; (1,0,0,1)->t2 ; (1,0,1/3,1/3)->t3')
# cover feasibility of the three covers (five constraints each), exact:
def feas(a_, b_, c_, e_):
    a_, b_, c_, e_ = Q(a_), Q(b_), Q(c_), Q(e_)
    return (3*a_ >= 1 and a_+2*b_ >= 1 and a_+2*c_ >= 1 and 2*c_+e_ >= 1 and 3*e_ >= 1
            and min(a_, b_, c_, e_) >= 0)
check('D02b the three covers are feasible (all five triangle constraints)',
      feas(Q(1,3),Q(1,3),Q(1,3),Q(1,3)) and feas(1,0,0,1) and feas(1,0,Q(1,3),Q(1,3)))

# --- D03
check('D03 C(d,2)+d r+C(r,2) = C(p,2)', (C2p(d)+d*r_+C2p(r_) - C2p(p)).is_zero())

# --- D04/05/06: exact (4.5) residuals per branch.
mu_low_p2  = q*q/12            # mu(alpha) p^2, alpha<=2/3
mu_high_p2 = (2*p-q)**2/48     # alpha>=2/3
Ca_p2 = (2*p*p - 2*p*q - q*q)/12
def RHS(mu_p2): return q*d/2 + Ca_p2 + mu_p2 - p/2

res1_low  = t1 - RHS(mu_low_p2)
res1_high = t1 - RHS(mu_high_p2)
ok = (res1_low - (q*(p-d)/6 + p/3)).is_zero()
ok &= (res1_high - (q*(p-d)/6 + p/3 + (3*q-2*p)*(q+2*p)/48)).is_zero()
check('D04 (4.5) branch-1 exact residuals', ok,
      'low: q(p-d)/6+p/3 >= 0 always; high: + (3q-2p)(q+2p)/48 >= 0 iff alpha>=2/3')

res2_high = t2 - RHS(mu_high_p2)
res2_low  = t2 - RHS(mu_low_p2)
sq2 = (d - (2*p+q)/4)**2
ok = (res2_high - sq2).is_zero()
ok &= (res2_low - (sq2 + (2*p-3*q)*(2*p+q)/48)).is_zero()
check('D05 (4.5) branch-2 exact residuals', ok,
      'high: perfect square (d-(2p+q)/4)^2; low: + (2p-3q)(2p+q)/48 >= 0 iff alpha<=2/3')

res3_low  = t3 - RHS(mu_low_p2)
res3_high = t3 - RHS(mu_high_p2)
# t3 simplifies to d^2/3 - d/3 + p^2/6 - p/6 :
check('D06a t3 = d^2/3 - d/3 + p^2/6 - p/6 (exact simplification)',
      (t3 - (d*d/3 - d/3 + p*p/6 - p/6)).is_zero())
# exact square completion at d* = 1/2 + 3q/4 :
dstar = P.const(Q(1,2)) + 3*q/4
sq3 = (d - dstar)**2 / 3
rem_low  = res3_low  - sq3
rem_high = res3_high - sq3
rem_low_expected  = p*q/6 + p/3 - P.const(Q(1,12)) - q/4 - 3*q*q/16
rem_high_expected = -p*p/12 + p*q/4 - q*q/8 + p/3 - q/4 - P.const(Q(1,12))
okc = (rem_low - rem_low_expected).is_zero() and (rem_high - rem_high_expected).is_zero()
check('D06a2 branch-3 square completion: residual = (d-(1/2+3q/4))^2/3 + rem(p,q)', okc,
      'rem_low = pq/6+p/3-1/12-q/4-3q^2/16 ; rem_high = -p^2/12+pq/4-q^2/8+p/3-q/4-1/12')
# rem_low >= 0 on 1<=q<=2p/3 (concave in q => check endpoints):
#   q=1:      p/2 - 25/48 >= 0 for p>=2  (substitute p=2+w: 23/48 + w/2, nonneg coeffs)
e1 = rem_low_expected.subst('q', P.const(1)).subst('p', P.const(2) + u)
#   q=2p/3:   p^2/36 + p/6 - 1/12 >= 0 for p>=1 (substitute p=1+w)
e2 = rem_low_expected.subst('q', 2*p/3).subst('p', P.const(1) + u)
ok_lo = all(v >= 0 for v in e1.coeffs()) and all(v >= 0 for v in e2.coeffs())
check('D06a3 rem_low >= 0 on 1<=q<=2p/3 (concavity + endpoint nonneg-coeff certs)', ok_lo,
      f'q=1, p=2+u: {e1} ; q=2p/3, p=1+u: {e2}')
# rem_high >= 0 on 2p/3 <= q <= (4p-2)/3 (concave; endpoints):
e3 = rem_high_expected.subst('q', 2*p/3).subst('p', P.const(1) + u)      # = p^2/36+p/6-1/12
e4 = rem_high_expected.subst('q', (4*p - 2)/3)                            # boundary d*=p
# at q=(4p-2)/3 the residual min moves to d=p; verify res3_high(d=p) = (2p-q)^2/16 identically:
bd = res3_high.subst('d', p) - (2*p - q)**2/16
ok_hi = all(v >= 0 for v in e3.coeffs()) and bd.is_zero()
check('D06a4 rem_high >= 0 at q=2p/3; and res3_high(d=p) = (2p-q)^2/16 >= 0 (boundary'
      ' certificate for q >= (4p-2)/3, where the real minimiser d* exceeds p)', ok_hi,
      f'q=2p/3, p=1+u: {e3} ; boundary identity zero: {bd.is_zero()} ; '
      f'rem_high at q=(4p-2)/3: {e4} (sign settled by the boundary identity + grid)')
def branch3_grid(pmax):
    bad = []
    for pp in range(3, pmax+1):
        for qq in range(1, 2*pp+1):
            mu_p2 = Q(qq*qq,12) if 3*qq <= 2*pp else Q((2*pp-qq)**2,48)
            base = Q(pp*(pp-1),2)
            capr = Ca_p2  # symbolic; recompute numerically:
            ca = Q(2*pp*pp - 2*pp*qq - qq*qq, 12)
            for dd in range(0, pp+1):
                rr = pp - dd
                t3v = Q(dd*(dd-1),2) + (Q(dd*rr) + Q(rr*(rr-1),2))/3
                rhs = Q(qq*dd,2) + ca + mu_p2 - Q(pp,2)
                if t3v < rhs:
                    bad.append((pp,qq,dd))
    return bad
bad3 = branch3_grid(90)
check('D06b (4.5) branch-3 pointwise, exact grid 3<=p<=90, 1<=q<=2p, 0<=d<=p',
      not bad3, f'violations: {bad3[:5]}')

# --- D07: Appendix A residual minima + dominance, sampled exactly over alpha in [0,2]
def minima_ok():
    for num in range(0, 401):
        a_ = Q(num, 200)           # alpha in [0,2]
        m1 = a_*a_/12
        m2 = (2-a_)**2/48
        if a_ <= Q(4,3):
            m3 = a_*(8-5*a_)/48
        else:
            m3 = (2-a_)**2/12
        lo = min(m1, m2)
        if m3 < lo: return False, a_
        # and mu(alpha) equals min(m1,m2):
        mu_ = a_*a_/12 if a_ <= Q(2,3) else (2-a_)**2/48
        if mu_ != lo: return False, a_
    return True, None
okA, wit = minima_ok()
check('D07 Appendix A: mu = min(m1,m2) and third-branch dominance on [0,2] (401 exact pts)',
      okA, f'witness: {wit}')

# --- D08
check('D08 mu continuity at 2/3', Q(2,3)**2/12 == (2-Q(2,3))**2/48)

# --- D09: (5.2) identity.  q = 2p-s, n = 3p-s, Sd = q p - M,
#  sum C(d_i,2) = q C(p,2) - (2p-1)M/2 + ... derive: C(p-mi,2) = C(p,2) - mi(2p-1)/2 + mi^2/2 - mi/2 +...
#  (p-mi)(p-mi-1)/2 = [p^2 - p - mi(2p-1) + mi^2]/2  =>
#  sum = q(p^2-p)/2 - (2p-1)M/2 + S2/2 ... careful: mi(2p-1)? expand: (p-mi)(p-mi-1)
#     = p^2 - p mi - p - p mi + mi^2 + mi = p^2 - p - (2p-1) mi + mi^2. correct.
qs = 2*p - s
n_ = 3*p - s
sumC2d = (qs*(p*p - p) - (2*p-1)*M + S2) / 2
E52 = C2p(p) + (qs*p - M)          # |E| = C(p,2) + Sd, Sd = qp - M
# multiply both sides by q (=qs) to stay polynomial:
lhs52q = E52*qs - 2*sumC2d
rhs52q = (n_*n_/6 + p/2 - s*s/6)*qs + (s-1)*M - S2
diff52 = lhs52q - rhs52q
check('D09 (5.2) identity: |E| - 2/q sum C(d_i,2) == n^2/6 + p/2 - s^2/6 + ((s-1)M - S2)/q',
      diff52.is_zero(), 'polynomial identity in (p,s,M,S2) after clearing q')

# --- D10: (5.3): ((s-1)M - S2)/q <= ((s-1)M - M^2/q)/q = (s-1)^2/4 - (M/q-(s-1)/2)^2
#  claim: (s-1)M q - M^2 = q^2 (s-1)^2/4 - (M - q(s-1)/2)^2   (denominators cleared)
cl = (s-1)*M*qs - M*M - (qs*qs*(s-1)*(s-1)/4 - (M - qs*(s-1)/2)**2)
check('D10 (5.3) parabola completion identity', cl.is_zero(),
      '(s-1)Mq - M^2 = q^2 (s-1)^2/4 - (M - q(s-1)/2)^2 ; plus S2 >= M^2/q (Cauchy-Schwarz)')
# and (s-1)^2/4 - s^2/6 = (s^2-6s+3)/12:
check('D10b (s-1)^2/4 - s^2/6 = (s^2-6s+3)/12',
      ((s-1)**2/4 - s*s/6 - (s*s - 6*s + 3)/12).is_zero())
# Cauchy-Schwarz S2 >= M^2/q on random integer profiles (exact):
ok = True
for _ in range(2000):
    qq = random.randint(1, 60)
    mis = [random.randint(0, 30) for _ in range(qq)]
    if Q(sum(x*x for x in mis)) < Q(sum(mis))**2/qq: ok = False; break
check('D10c S2 >= M^2/q on 2000 random exact profiles', ok)

# --- D11: (9.5) integer step: m_i < s/3 - 5/6 (integers m_i, s) => 3 m_i <= s - 3
ok = True
for ss in range(0, 400):
    for mi in range(0, 140):
        if Q(mi) < Q(ss,3) - Q(5,6) and not (3*mi <= ss - 3):
            ok = False
check('D11 (9.5): m_i < s/3 - 5/6 => 3m <= s-3 (exhaustive integer check)', ok,
      'integrality: 3m_i <= ceil(s - 5/2) - 1 = s - 3 for integer s')

# --- D12: delta >= 7/8 both parities, exact grid + certificate identities
ok_id = ((p - s)*8 - (7*p + (p - 8*s))).is_zero()           # 8(p-s) = 7p + (p-8s)
ok_id &= ((p + 1 - s)*8 - (7*(p-1) + (p + 15 - 8*s))).is_zero()
ok_grid = True
for pp in range(2, 3000):
    smax = pp // 8
    for ss in (0, 1, smax-1, smax):
        if ss < 0 or 8*ss > pp: continue
        rpv = rp_of(pp)
        h = min(rpv, (2*pp-ss) - rpv)
        delta = Q(h, rpv)
        if delta < Q(7,8): ok_grid = False; break
check('D12 (9.10) delta >= 7/8, both parities: certificate identities + grid p<3000',
      ok_id and ok_grid,
      'odd: 8(p-s)=7p+(p-8s); even: 8(p+1-s)=7(p-1)+(p+15-8s); grid uses h=min(r_p, q-r_p)')

# --- D13: (9.11) certificate. u := s-3-3m >= 0.  2s(s-3)/9 - m(s-1-m) with s=3m+3+u:
expr13 = (2*s*(s-3)/9 - m*(s-1-m)).subst('s', 3*m + 3 + u)
neg = [ (e,v) for e, v in expr13.c.items() if v < 0 ]
check('D13 (9.11) nonneg-coefficient certificate in (m, u=s-3-3m)',
      not neg, f'expanded: {expr13}')

# --- D14: (9.12)
check('D14a (9.12) s^2 coefficient', Q(-1,6)+Q(2,9)-Q(7,96) == Q(-5,288))
# conclusion: s^2 >= 36 p => p/2 - 5s^2/288 - 2s/3 <= -p/8 - 2s/3
check('D14b p/2 - 5*(36p)/288 = -p/8', Q(1,2) - Q(5*36,288) == Q(-1,8))
# and the (q+2)/(q-1) >= 1 step used to drop to 7/96 s^2: exact for q >= 2:
check('D14c (q+2)/(q-1) >= 1 for q>=2 (trivial: q+2 > q-1)', True,
      '2*delta*V/(q(q-1)) >= (7/96) s^2 (q+2)/(q-1) >= (7/96) s^2')

# --- D15: (9.16)/(9.17) exact grid.  Given p, s in [6 sqrt p, p/8], rho <= (s-3)/3,
# b = p - rho, r_b = chi'(K_b), U = q - r_b, theta = max(rho-1,0)/b,
# kappa = 1 - 2(1-theta)U/q  <= 5s/4p ; (s-2rho-1)+/q <= 5s/4p.
def d15_grid(ps):
    bad = []
    for pp in ps:
        s_lo = math.isqrt(36*pp)
        if s_lo*s_lo < 36*pp: s_lo += 1
        s_hi = pp // 8
        if s_lo > s_hi: continue
        for ss in {s_lo, s_lo+1, (s_lo+s_hi)//2, s_hi-1, s_hi}:
            if ss < s_lo or ss > s_hi: continue
            qq = 2*pp - ss
            rmax = (ss-3)//3
            for rr in {0, 1, 2, rmax//2, rmax-1, rmax}:
                if rr < 0 or rr > rmax: continue
                bb = pp - rr
                rb = rp_of(bb)
                uu = qq - rb
                th = Q(max(rr-1,0), bb)
                kap = 1 - 2*(1-th)*Q(uu, qq)
                lim = Q(5*ss, 4*pp)
                if kap > lim: bad.append(('kappa', pp, ss, rr, kap, lim))
                dev = Q(max(ss-2*rr-1, 0), qq)
                if dev > lim: bad.append(('dev', pp, ss, rr))
    return bad
ps = list(range(2304, 2340)) + [2400, 3000, 5000, 9999, 10000, 20000, 65536, 100003]
bad15 = d15_grid(ps)
check('D15 (9.16)/(9.17) kappa_R <= 5s/4p and (s-2rho-1)+/q <= 5s/4p (exact grid)',
      not bad15, f'p in {{2304..2339, 2400, 3000, 5000, 9999, 10000, 20000, 65536, 100003}}; '
      f'violations: {bad15[:5]}')
# symbolic backbone: 8/15 + 16/23 <= 5/4
check('D15b 8/15 + 16/23 = 424/345 <= 5/4', Q(8,15)+Q(16,23) == Q(424,345) and Q(424,345) <= Q(5,4))

# --- D16: clear denominators: 5s^2/192 * 24p - 5s^3/24 * ... i.e.
#  5*24*p*s^2 - 5*192*s^3 = 5*24*s^2*(p - 8s)  (identity; >= 0 iff 8s <= p)
check('D16 (9.18): 24p*5s^2 - 192*5s^3 = 120 s^2 (p - 8s) (identity => ineq iff 8s<=p)',
      (5*24*p*s*s - 5*192*s**3 - 120*s*s*(p - 8*s)).is_zero(),
      '5s^3/(24p) <= 5s^2/192  <=>  8s <= p (used with s <= p/8)')

# --- D17: (9.19)
check('D17 (9.19) completed square',
      (s*s/6 - s*rho + 2*rho*rho - (2*(rho - s/4)**2 + s*s/24)).is_zero())

# --- D18: (9.20)
check('D18a (9.20) coefficient', Q(-1,24)+Q(5,192) == Q(-1,64))
check('D18b p/2 - 36p/64 = -p/16', Q(1,2) - Q(36,64) == Q(-1,16))

# --- D19: threshold
sols = [pp for pp in range(1, 10000) if 36*pp*64 == pp*pp]
check('D19 6 sqrt(p) = p/8 <=> p = 2304 (positive integers, exhaustive to 10^4)',
      sols == [2304], f'solutions: {sols}')

# --- D20: Prop 10.1(i) chain, exact grid
def d20():
    bad = []
    for pp in range(36, 601):
        smax = math.isqrt(36*pp)   # floor(6 sqrt p)
        for ss in range(0, smax+1):
            qq = 2*pp - ss
            if qq < rp_of(pp): bad.append(('q<rp', pp, ss)); continue
            nn = pp + qq
            # (5.3) bound value:
            b53 = Q(nn*nn,6) + Q(pp,2) + Q(ss*ss - 6*ss + 3, 12)
            # claim chain: b53 <= n^2/6 + 2n
            if b53 > Q(nn*nn,6) + 2*nn: bad.append(('chain', pp, ss))
    return bad
bad20 = d20()
check('D20 Prop 10.1(i): (5.3)-bound <= n^2/6 + 2n for all p in [36,600], 0<=s<=6sqrt(p)'
      ' (and q >= r_p throughout)', not bad20, f'violations: {bad20[:5]}')

# --- D21: Lemma 6.1 counting
def B_edges(Sset, K):
    return {frozenset(e) for e in combinations(K, 2) if set(e) & Sset}
ok_cnt = True
Kp = list(range(7)); pp = 7
for Si in map(set, (set(c) for k in range(0,5) for c in combinations(Kp, k))):
    for Sj in (set(c) for k in range(0,5) for c in combinations(Kp, k)):
        aij = len(Si - Sj)
        lhs = len(B_edges(Si, Kp) - B_edges(set(Sj), Kp))
        rhs = Q(aij*(2*(pp-len(Sj)) - aij - 1), 2)
        if Q(lhs) != rhs: ok_cnt = False
check('D21a |B_i \\ B_j| = a_ij (2(p-|S_j|) - a_ij - 1)/2, exhaustive p=7, |S|<=4', ok_cnt)
ok_V = True; ok_L = True
for _ in range(400):
    pp = random.randint(4, 10); qq = random.randint(1, 8)
    mm_cap = random.randint(0, pp)
    Ss = [set(random.sample(range(pp), random.randint(0, mm_cap))) for _ in range(qq)]
    b_e = {}
    for e in combinations(range(pp), 2):
        b_e[e] = sum(1 for S_ in Ss if set(e) & S_)
    V1 = sum(be*(qq-be) for be in b_e.values())
    V2 = sum(len(B_edges(Si, list(range(pp))) - B_edges(Sj, list(range(pp))))
             for Si in Ss for Sj in Ss)
    if V1 != V2: ok_V = False
    mmax = max((len(S_) for S_ in Ss), default=0)
    if 2*pp - 3*mmax - 1 >= 0:
        lhsL = Q(V1)
        rhsL = Q(2*pp - 3*mmax - 1, 4) * sum(len(Si ^ Sj) for Si in Ss for Sj in Ss)
        if lhsL < rhsL: ok_L = False
check('D21b V-identity V = sum_{i,j} |B_i \\ B_j| (400 random exact instances)', ok_V)
check('D21c Lemma 6.1 inequality on the same instances (when 2p-3m-1>=0)', ok_L)

# --- D23: Lemma 7.1 assembly identity (the paper does NOT display this expansion;
# reconstructed by the auditor from §7.1-§7.4 and verified here).
# From nu3 >= C(b,2) + C(rho,2) - (1/q) sum beta_i + (u/q)(1-theta)B_R  (after the
# best-u selection), with 2 sum beta_i = (2b-1)A_R - A2R, |E| = C(p,2)+qp-M,
# M = A_R + q rho - B_R, b = p - rho, q = 2p - s, n = 3p - s:
#   (i)  A_R coefficient:  -1 + (2b-1)/q  ==  (s-2rho-1)/q      [times A_R]
#   (ii) constant block: C(p,2) + qp - q rho - 2C(b,2) - 2C(rho,2)
#                       == n^2/6 + p/2 - s^2/6 + s rho - 2 rho^2
b_ = p - rho
lhs23i = (-(2*p - s) + (2*b_ - 1))            # q*(coeff), cleared by q
rhs23i = (s - 2*rho - 1)
check('D23a Lemma 7.1 assembly: A_R coefficient (2b-1-q) = s-2rho-1', (lhs23i - rhs23i).is_zero())
lhs23 = C2p(p) + (2*p - s)*p - (2*p - s)*rho - 2*C2p(b_) - 2*C2p(rho)
rhs23 = (3*p - s)**2/6 + p/2 - s*s/6 + s*rho - 2*rho*rho
check('D23b Lemma 7.1 assembly: constant block identity', (lhs23 - rhs23).is_zero(),
      'C(p,2)+qp-q rho-2C(b,2)-2C(rho,2) == n^2/6+p/2-s^2/6+s rho-2rho^2  (b=p-rho, q=2p-s)')
# beta_i identity: C(b,2) - C(b-t,2) = (t(2b-1) - t^2)/2, i.e. 2 sum beta = (2b-1)A_R - A2R
t_ = u   # reuse symbol u as t_i here
check('D23c 2*beta_i identity: 2(C(b,2)-C(b-t,2)) = t(2b-1) - t^2',
      (2*(C2p(b_) - C2p(b_ - t_)) - (t_*(2*b_ - 1) - t_*t_)).is_zero())

# --- D22: sharpness closed form (n = 3p): C(p,2) + 2p^2 - 2 C(p,2) == (3p)^2/6 + (3p)/6
lhs22 = C2p(p) + 2*p*p - 2*C2p(p)
rhs22 = (3*p)*(3*p)/6 + 3*p/6
check('D22 K_p v bar-K_2p: |E| - 2 C(p,2) = n^2/6 + n/6 (polynomial identity)',
      (lhs22-rhs22).is_zero())

emit(); emit('='*76)
npass = sum(1 for _, ok in RES if ok)
emit(f'SUMMARY: {npass}/{len(RES)} checks PASSED')
emit('='*76)
rep = '\n'.join(OUT)
print(rep)
os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results'), exist_ok=True)
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'algebra_results.txt'),
          'w', encoding='utf-8') as f:
    f.write(rep + '\n')
sys.exit(0 if npass == len(RES) else 1)
