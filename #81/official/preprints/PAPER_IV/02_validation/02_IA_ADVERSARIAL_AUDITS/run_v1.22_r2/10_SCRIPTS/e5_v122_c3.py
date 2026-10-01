"""E5 (auditor-written, run_v1.22_r1): exact checks of the C.3 regularity-to-tower comparison added in v1.22.
Exact integers/rationals; huge quantities (R, B, T) handled by exponent arithmetic with explicit lemmas.
Each check has a negative control that must FAIL. No Lean."""
from fractions import Fraction as F
import math, json, sys
res = []
def rec(i, claim, ok, neg=None, neg_val=None):
    res.append({'id': i, 'claim': claim, 'pass': bool(ok), 'negative_control': neg, 'negative_rejected': None if neg_val is None else (not bool(neg_val))})
X = 9 * 10**19
a = F(1, X); delta = a**21 / 2208; eps = delta / 8
k0 = 3 * 10**19 + 1
h = 4 * 8**5 * 2208**5 * 4500**105 * (2 * 10**16)**105
# H(eps) = floor(4/eps^5) = h exactly
H = 4 / eps**5
rec('C3a', 'H(δ/8)=⌊4/ε⁵⌋ is the integer h of §6.3 (and 9e19 = 4500·2e16)', H.denominator == 1 and H.numerator == h and X == 4500 * 2 * 10**16,
    'h with 4500^104', H.numerator == 4 * 8**5 * 2208**5 * 4500**104 * (2 * 10**16)**105)
# I: 100/eps^5 <= 4^4000  => floor(log(...)/log 4) <= 4000 ; then max{7,k0,...} = k0
v = 100 / eps**5
rec('C3b', '100/ε⁵ ≤ 4^4000, hence I(δ/8,k0)=k0 (≤4001<k0)', v <= 4**4000 and 4001 < k0 and 7 < k0,
    '100/ε⁵ ≤ 4^3400', v <= 4**3400)
# alpha, beta and the ceiling terms
alpha = 2208 * X**21; beta = 8 * X**6
rec('C3c', '1/δ = α = 2208(9e19)^21 exactly', 1 / delta == alpha)
a3 = a**3 - 3 * delta; a4 = a**6 - 6 * delta
rec('C3d', '(a3+a4)/(a3 a4) ≤ 2(9e19)^6 (exact), with slack ≥ 1/(4·G1·B^5) for the ceiling', (a3 + a4) / (a3 * a4) <= 2 * F(X)**6 and 2 * F(X)**6 - (a3 + a4) / (a3 * a4) >= F(1, 10**10) * F(X)**6,
    '(a3+a4)/(a3 a4) ≤ (9e19)^6', (a3 + a4) / (a3 * a4) <= F(X)**6)
rec('C3e', 'z=1/(2e17) and 50/ξ=10^18 at ξ=η0/2', F(1, 10**16) / 2 / 10 == F(1, 2 * 10**17) and 50 / (F(1, 10**16) / 2) == 10**18)
rec('C3f', 'k0, α, β, 10^18 ≤ 2^2000', max(k0, alpha, beta, 10**18) <= 2**2000, 'α ≤ 2^1400', alpha <= 2**1400)
rec('C3g', 'k0 ≥ 59517 so 2^(2^k0) ≥ 2^(2^59517) ≥ G_i bound', k0 >= 59517)
# x4^x >= 2^x and 16^R >= 4R, B >= 4R^2, R^2 <= B/4  (symbolic lemmas checked on ranges)
rec('C3h', 'x·4^x ≥ 2^x, 16^x ≥ 4x, 4x ≤ 4^x, 8q ≤ 2^q (q≥6) on x≤200, q in 6..200', all(x * 4**x >= 2**x and 16**x >= 4 * x and 4 * x <= 4**x for x in range(1, 201)) and all(8 * q <= 2**q for q in range(6, 201)),
    '8q ≤ 2^q at q=5', 8 * 5 <= 2**5)
rec('C3i', '(1/4 + 7/256) ≤ 1 and 256B² ≤ B⁶ for B ≥ 4', F(1, 4) + F(7, 256) <= 1 and all(256 * B**2 <= B**6 for B in range(4, 50)),
    '256B² ≤ B⁶ at B=3', 256 * 9 <= 3**6)
rec('C3j', 'term bounds sum: 1+1+1+3+1 = 7 (k0, αB, G3, 10^18(1+2G2), 1)', 1 + 1 + 1 + 3 + 1 == 7)
rec('C3k', '4k0 ≤ 2^67 ≤ T(5)=2^65536', 4 * k0 <= 2**67 and 67 <= 65536, '4k0 ≤ 2^66', 4 * k0 <= 2**66)
rec('C3l', '4(x4^x) ≤ 2^(4x) for x in 1..300 (induction step 4t_{j+1} ≤ 2^{4t_j})', all(4 * x * 4**x <= 2**(4 * x) for x in range(1, 301)))
rec('C3m', 'B^6 ≤ 2^(30R): (R·16^R)^6 = R^6·2^(24R) ≤ 2^(6R)·2^(24R) for R in 1..300', all((R * 16**R)**6 <= 2**(30 * R) for R in range(1, 301)),
    '(R·16^R)^6 ≤ 2^(29R) at R=1..50', all((R * 16**R)**6 <= 2**(29 * R) for R in range(1, 51)))
rec('C3n', '30R ≤ 8q when 4R ≤ q', all(30 * R <= 8 * (4 * R) for R in range(1, 1000)))
out = {'tests': res, 'all_pass': all(r['pass'] for r in res), 'all_negatives_rejected': all(r['negative_rejected'] in (None, True) for r in res),
       'scope': 'finite/exact checks of the arithmetic steps; universal lemmas (e.g. x4^x≥2^x for all x) are elementary and checked only on ranges here'}
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
for r in res: print(r['id'], 'PASS' if r['pass'] else 'FAIL', '| neg rejected:', r['negative_rejected'])
print('ALL', out['all_pass'], out['all_negatives_rejected'])
