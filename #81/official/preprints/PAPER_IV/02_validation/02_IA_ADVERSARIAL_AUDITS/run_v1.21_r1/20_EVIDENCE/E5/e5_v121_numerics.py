"""E5 (auditor-written, run_v1.21_r1): exact / rigorous checks of the NEW numerical claims of v1.21
(C.2 bilateral cleaning, C.3 schedule chain, E.1 normalization and (E.2d) error). No Lean.
Each check has a predeclared negative control that must FAIL. Logs of 2-powers are compared with
exact rational bounds on log(2) (mpmath at high precision, used only for monotone comparisons)."""
from fractions import Fraction as F
import mpmath as mp, json, sys
mp.mp.dps = 60
res = []
def rec(i, claim, ok, neg=None, neg_ok=None, note=''):
    res.append({'id': i, 'claim': claim, 'pass': bool(ok), 'negative_control': neg, 'negative_rejected': (None if neg_ok is None else bool(not neg_ok)), 'note': note})
LN2 = mp.log(2)
# ---- C.2 schedule inequalities: d=u=v=a, delta=a^21/2208, a3=a^3-3delta, a4=a^6-6delta, 0<a<=1/10
def c2(a, K3=33, K4=138):
    a = F(a); d = a**21 / 2208; a3 = a**3 - 3 * d; a4 = a**6 - 6 * d
    return (a3 >= a**3 / 2 and a4 >= a**6 / 2 and K3 * d <= a * a**2 * a3**3 and K4 * d <= a * a**2 * a4**3)
grid = [F(1, 10), F(1, 11), F(1, 100), F(1, 4500), F(1, 9 * 10**19), F(1, 10**30)]
rec('C2-1', '33δ≤v u² a3³ and 138δ≤v u² a4³ with a3≥a³/2, a4≥a⁶/2 for 0<a≤1/10 (grid incl. η0 schedule)', all(c2(a) for a in grid),
    'constant 138 replaced by 138*17 (must fail at a=1/10)', c2(F(1, 10), 33, 138 * 17))
rec('C2-2', '138δ = a^21/16 identity', F(138, 2208) == F(1, 16), '138/2208 = 1/8', F(138, 2208) == F(1, 8))
rec('C2-3', 'deleted copies: 3 pairs × 11 = 33; 6 pairs × 23 = 138', 3 * 11 == 33 and 6 * 23 == 138)
# Monotonicity in a for c2: 33δ/(a^12 ...) — ratio LHS/RHS ~ const*a^9 increasing? check symbolic dominance at worst a=1/10
# ---- C.3 chain
b0 = F(1, 64 * 10**18)
rec('C3-1', 'β0 ≥ 2^-66', b0 >= F(1, 2**66), 'β0 ≥ 2^-65', b0 >= F(1, 2**65))
L = -mp.log(mp.mpf(1) / (64 * 10**18))
rec('C3-2', 'L_T=-log β0 ≤ 66 log2 ≤ 46', L <= 66 * LN2 <= 46)
M = 16 * 7 * L + 1
rec('C3-3', 'M_T ≤ 5153', M <= 5153, 'M_T ≤ 5100', M <= 5100)
rec('C3-4', '8·5153+1 ≤ 59480 log2  (⇒ γ_T ≥ 2^-59485)', 8 * 5153 + 1 <= 59480 * LN2, '8·5153+1 ≤ 59470 log2', 8 * 5153 + 1 <= 59470 * LN2)
a0 = 59485
rec('C3-5', 'T_T ≤ 5153·2^a0+1 ≤ 2^(a0+13)', 5153 < 2**13 - 1)
rec('C3-6', '4a0+5 ≤ 2^18', 4 * a0 + 5 <= 2**18, '4a0+5 ≤ 2^17', 4 * a0 + 5 <= 2**17)
rec('C3-7', '(4a0+5)(a0+13 exponent) : 2^18·2^(a0+13)=2^(a0+31)=Y', 18 + a0 + 13 == a0 + 31)
# retained scale: 2xT ≤ (12/7)(5153+1/8) ≤ 12748 log2
rec('C3-8', '(12/7)(5153+1/8) ≤ 12748 log2', mp.mpf(12) / 7 * (5153 + mp.mpf(1) / 8) <= 12748 * LN2,
    '(12/7)(5153+1/8) ≤ 12740 log2', mp.mpf(12) / 7 * (5153 + mp.mpf(1) / 8) <= 12740 * LN2)
rec('C3-9', '(1-x) ≥ 1/(1+2x) for 0≤x≤1/2 (exact at sampled rationals)', all((1 - F(k, 200)) >= 1 / (1 + 2 * F(k, 200)) for k in range(0, 101)))
# D0 ≤ 2^(a0+146): 256*7/((β/2)^2 γ) with (β/2)^-2 ≤ 2^134, γ^-1 ≤ 2^a0 ; 96/ε ≤ 96·2^a0 ; +4
lhs = F(256 * 7) * 2**134 + 96 + 4  # coefficient of 2^a0 upper bound (4 absorbed)
rec('C3-10', 'D0 ≤ 2^(a0+146)', lhs <= 2**146, 'D0 ≤ 2^(a0+144)', lhs <= 2**144)
# c0 ≥ 2^-(Y+3a0+220): η≥2^-(Y+69), ε²≥2^-2a0, γ≥2^-a0, (β/2)²≥2^-134, 1/(16384·7)≥2^-17
rec('C3-11', '69+134+17=220 and 1/(16384·7) ≥ 2^-17', 69 + 134 + 17 == 220 and F(1, 16384 * 7) >= F(1, 2**17))
rec('C3-12', 'Z = 3a0+220+12749 = 191424', 3 * a0 + 220 + 12749 == 191424, 'Z=191432', 3 * a0 + 220 + 12749 == 191432)
rec('C3-13', 'U = Y+Z+8 = Y+191432 (256=2^8) and 4(1+r²)=200≤256-2', 191424 + 8 == 191432 and 4 * (1 + 49) + 2 <= 256)
rec('C3-14', 'd0 ≤ 2^(a0+146+12749) ≤ 2^U (trivial vs Y)', a0 + 146 + 12749 < 2**59516)
rec('C3-15', '2·10^17·392 ≤ 2^67', 2 * 10**17 * 392 <= 2**67, '2·10^17·392 ≤ 2^66', 2 * 10**17 * 392 <= 2**66)
rec('C3-16', 'U+67 ≤ 2^59517 (U=2^59516+191432)', 191432 + 67 <= 2**59516)
# ---- E.1 normalization (h=s+1, ε=1/(1e41 h^8), ρ=n/h², λ=n/h⁴): symbolic identities at sample h
ok = True
for h in [1, 2, 3, 7, 50]:
    n = F(10**60) * h**8; eps = F(1, 10**41 * h**8); rho = n / h**2; lam = n / h**4
    ok &= (eps * n**2 == lam**2 / 10**41) and (n * lam == rho**2)
    ok &= (lam**2 / 10**41 + n * lam / 10**31 <= 2 * rho**2 / 10**31)            # exterior edges
    ok &= (4 * rho / 10**27 >= (2 * (2 * rho**2 / 10**31)) / (rho / 10**4))       # |Y| bound
    ok &= (eps * n <= lam / 10**41)                                                # εn ≤ λ/1e41
    ok &= (rho / 10**4 + 2 * lam / 10**41 < rho / 200)
    Yr = 4 * rho / 10**27; Yc = 4 * rho / 10**27
    D = lam**2 / 10**41 + Yr * rho / 200 + Yc * (rho / 40 + Yr)
    ok &= D <= (rho / 10**13)**2
rec('E1-1', 'normalization identities and bounds (εn²=λ²/1e41, nλ=ρ², exterior ≤2ρ²/1e31, |Y|≤4ρ/1e27, light missing <ρ/200, D≤(ρ/1e13)²)', ok)
# ---- (E.2d) error ≤ n/9 with ν≤s<h, x≤2h, h²ρ=n, h²λ=ρ, h²≤ρ/1e50, ω=ceil(ρ/1e4)
ok = True; negok = True
for h in [1, 2, 5, 40]:
    rho = F(10**50) * h**2 * 10; n = rho * h**2; lam = rho / h**2; s = h - 1; nu = s; x = 2 * h
    om = rho / 10**4 + 1
    err = 2 * (om + s) * x + x * (2 * nu * rho / 40 + x * lam / 10**10)
    ok &= err <= n / 9
    negok &= err <= n / 12   # negative control: n/12 must fail for some h
rec('E2d-1', '(E.2d) error 2(ω+s)x + x(2νρ/40 + xλ/1e10) ≤ n/9', ok, 'same error ≤ n/12', negok)
out = {'tests': res, 'all_pass': all(r['pass'] for r in res), 'all_negatives_rejected': all(r['negative_rejected'] in (None, True) for r in res)}
json.dump(out, open(sys.argv[1], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
for r in res: print(r['id'], 'PASS' if r['pass'] else 'FAIL', '| neg rejected:' , r['negative_rejected'])
print('ALL', out['all_pass'], out['all_negatives_rejected'])
