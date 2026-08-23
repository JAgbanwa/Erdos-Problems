"""
Paper III — INTERNAL AUDIT, Block 01: algebraic identities.

Symbolic (exact) verification with SymPy of every closed-form identity the paper's
audit relies on (LEDGER "Audit status" line). Each check is proved as an identity in
the polynomial ring Q[p,q,d,s,rho,...] (i.e. `simplify(LHS - RHS) == 0`), or as an
exact rational (in)equality. Results are written to results/identities_results.txt.

Claims audited (paper tags in brackets):
  I1  T(G) key identity of Theorem 4.2:  T = (1/2)Sum d_i + C_alpha p^2 - p/4
  I2  (9.12) s^2 coefficient:  -1/6 + 2/9 - 7/96 = -5/288
  I3  (9.19) completed square:  s^2/6 - s*rho + 2*rho^2 = 2(rho - s/4)^2 + s^2/24
  I4  (9.19) lower bound:  s^2/6 - s*rho + 2*rho^2 >= s^2/24
  I5  (9.20) coefficient:  -1/24 + 5/192 = -1/64
  I6  (9.10) delta>=7/8, p odd:   (p-s)/p >= 7/8  for 0<=s<=p/8, p>0
  I7  (9.10) delta>=7/8, p even:  (p+1-s)/(p-1) >= 7/8  for 0<=s<=p/8, p>=2
  I8  corridor threshold:  36 p = p^2/64  <=>  p = 2304   (squared form of 6*sqrt(p)=p/8)
  I9  mu well-defined at breakpoint alpha=2/3:  (2/3)^2/12 = (2-2/3)^2/48
  I10 F-branch completion (4.5) identities: C_alpha p^2 and mu p^2 closed forms
"""
import sympy as sp

OUT = []


def emit(line=""):
    OUT.append(str(line))


p, q, d, s, rho, a = sp.symbols('p q d s rho alpha', positive=True)
Sd = sp.symbols('Sd')  # stands for Sum_i d_i

emit("=" * 72)
emit("Paper III — Block 01: algebraic identities (SymPy exact symbolic audit)")
emit("=" * 72)
emit()

results = []


def check_zero(name, expr, note=""):
    val = sp.simplify(expr)
    ok = (val == 0)
    results.append((name, ok))
    emit(f"[{'PASS' if ok else 'FAIL'}] {name}")
    if note:
        emit(f"        {note}")
    emit(f"        simplify(LHS - RHS) = {val}")
    emit()
    return ok


def check_true(name, cond, note=""):
    ok = bool(cond)
    results.append((name, ok))
    emit(f"[{'PASS' if ok else 'FAIL'}] {name}")
    if note:
        emit(f"        {note}")
    emit(f"        evaluated: {cond}")
    emit()
    return ok


# I1: T(G) key identity. |E| = C(p,2) + Sd ; alpha = q/p.
# T = (|E| - (p+q)^2/6)/2 ;  claim T = Sd/2 + C_alpha p^2 - p/4 with C_alpha=(2-2a-a^2)/12, a=q/p.
E = p * (p - 1) / 2 + Sd
alpha = q / p
Ca = (2 - 2 * alpha - alpha ** 2) / 12
T_lhs = (E - (p + q) ** 2 / 6) / 2
T_rhs = Sd / 2 + Ca * p ** 2 - p / 4
check_zero("I1  T(G) key identity (Thm 4.2)", T_lhs - T_rhs,
           "T = 1/2 Sum d_i + C_alpha p^2 - p/4, alpha=q/p, |E|=C(p,2)+Sum d_i")

# I2: (9.12) coefficient
check_zero("I2  (9.12) s^2 coefficient",
           (sp.Rational(-1, 6) + sp.Rational(2, 9) - sp.Rational(7, 96)) - sp.Rational(-5, 288),
           "-1/6 + 2/9 - 7/96 = -5/288")

# I3: (9.19) completed square
lhs19 = s ** 2 / 6 - s * rho + 2 * rho ** 2
rhs19 = 2 * (rho - s / 4) ** 2 + s ** 2 / 24
check_zero("I3  (9.19) completed square", lhs19 - rhs19,
           "s^2/6 - s*rho + 2*rho^2 = 2(rho - s/4)^2 + s^2/24")

# I4: (9.19) lower bound  s^2/6 - s*rho + 2*rho^2 >= s^2/24  (since 2(rho-s/4)^2 >= 0)
diff19 = sp.simplify(lhs19 - s ** 2 / 24)  # = 2(rho - s/4)^2
# prove nonneg: it equals 2*(rho - s/4)^2 which is a square times 2
is_sq = sp.simplify(diff19 - 2 * (rho - s / 4) ** 2) == 0
check_true("I4  (9.19) lower bound >= s^2/24", is_sq,
           "difference equals 2*(rho - s/4)^2 >= 0 (sum of squares certificate)")

# I5: (9.20) coefficient
check_zero("I5  (9.20) coefficient",
           (sp.Rational(-1, 24) + sp.Rational(5, 192)) - sp.Rational(-1, 64),
           "-1/24 + 5/192 = -1/64")

# I6: delta>=7/8 p odd: (p-s)/p >= 7/8 for s<=p/8.  Worst case s=p/8: (p-p/8)/p = 7/8.
# Show (p-s)/p - 7/8 >= 0 given s<=p/8:  = (p/8 - s)/p >= 0.
expr_odd = (p - s) / p - sp.Rational(7, 8)
expr_odd_simpl = sp.simplify(expr_odd - (p / 8 - s) / p)
check_true("I6  (9.10) delta>=7/8 (p odd)", expr_odd_simpl == 0,
           "(p-s)/p - 7/8 = (p/8 - s)/p >= 0 when s<=p/8, p>0")

# I7: p even: (p+1-s)/(p-1) >= 7/8 for s<=p/8, p>=2.
# (p+1-s)/(p-1) - 7/8 = (8(p+1-s) - 7(p-1))/(8(p-1)) = (p + 15 - 8s)/(8(p-1)).
# With s<=p/8: p - 8s >= 0, so numerator >= 15 > 0.
num_even = sp.simplify(8 * (p + 1 - s) - 7 * (p - 1))
check_true("I7  (9.10) delta>=7/8 (p even)", sp.simplify(num_even - (p + 15 - 8 * s)) == 0,
           "(p+1-s)/(p-1) - 7/8 = (p + 15 - 8s)/(8(p-1)); p-8s>=0 => numerator>=15>0")

# I8: corridor threshold 36 p = p^2/64 <=> p = 2304 (for p>0)
sol = sp.solve(sp.Eq(36 * p, p ** 2 / 64), p)
sol_pos = [x for x in sol if x != 0]
check_true("I8  corridor threshold p=2304", sol_pos == [2304],
           "36 p = p^2/64  <=>  p in {0, 2304}; positive root = 2304 (i.e. 6*sqrt(p)=p/8)")

# I9: mu breakpoint continuity at alpha=2/3
check_zero("I9  mu continuity at alpha=2/3",
           (sp.Rational(2, 3) ** 2 / 12) - ((2 - sp.Rational(2, 3)) ** 2 / 48),
           "(2/3)^2/12 = (2-2/3)^2/48")

# I10: F-branch completion closed forms used in (4.5)
#   C_alpha(q/p) p^2 = (2p^2 - 2qp - q^2)/12
check_zero("I10a C_alpha(q/p) p^2 closed form",
           ((2 - 2 * (q / p) - (q / p) ** 2) / 12) * p ** 2 - (2 * p ** 2 - 2 * q * p - q ** 2) / 12,
           "C_alpha(q/p) p^2 = (2p^2 - 2qp - q^2)/12")
#   mu low branch: (q/p)^2/12 * p^2 = q^2/12
check_zero("I10b mu low-branch closed form",
           ((q / p) ** 2 / 12) * p ** 2 - q ** 2 / 12,
           "mu_low(q/p) p^2 = q^2/12")
#   mu high branch: (2-q/p)^2/48 * p^2 = (2p-q)^2/48
check_zero("I10c mu high-branch closed form",
           ((2 - q / p) ** 2 / 48) * p ** 2 - (2 * p - q) ** 2 / 48,
           "mu_high(q/p) p^2 = (2p-q)^2/48")

emit("=" * 72)
npass = sum(1 for _, ok in results if ok)
emit(f"SUMMARY: {npass}/{len(results)} identity checks PASSED")
emit("=" * 72)

report = "\n".join(OUT)
print(report)
with open("results/identities_results.txt", "w", encoding="utf-8") as f:
    f.write(report + "\n")

import sys
sys.exit(0 if npass == len(results) else 1)
