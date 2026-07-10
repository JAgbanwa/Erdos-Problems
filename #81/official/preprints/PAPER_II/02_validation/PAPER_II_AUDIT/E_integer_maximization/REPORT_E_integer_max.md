---
geometry: margin=1in
fontsize: 11pt
---
# Independent Computational Verification
## Paper II — Section 7: exact integer maximization (Prop 7.1, Theorem 1.1 arithmetic)

**Author of record:** Juan Pablo Traverso Gianini  **Date:** 2026-07-09  
**Artifact:** `E_integer_maximization/audit_E_integer_max.py`  **Verdict: PASS**

### Scope
**Every** integer $n$ from $1$ to $2000$, in **exact rational arithmetic** (`fractions`).

### Claims verified
- **(E1) Theorem 1.1 value:** $\displaystyle\max_{p+q=n}\Phi_\tau(S_{p,q})=\left\lfloor\tfrac{(2n+1)^2}{24}\right\rfloor$.
- **(E2) maximizer:** the maximum is attained in the **saturated** branch ($q\ge p-1$) by the
  integer $p$ nearest to $(2n+1)/6$.
- **(E3):** the **non-saturated** branch never exceeds the floor.
- **(E4) residue identity:** $(2n+1)^2\equiv 1$ or $9 \pmod{24}$, matching the closed floor.

### Results
- E1 violations: **0**
- E2 violations: **0**
- E3 violations: **0**
- E4 violations: **0**
- **Total violations over all $n\le2000$: 0.** Runtime 19.9 s.

| $n$ | $\lfloor (2n+1)^2/24\rfloor$ | maximizer $p^{*}$ |
|----|----|----|
| 1 | 0 | 1 |
| 2 | 1 | 1 |
| 3 | 2 | 1 |
| 5 | 5 | 2 |
| 8 | 12 | 3 |
| 12 | 26 | 4 |
| 13 | 30 | 5 |
| 50 | 425 | 17 |
| 100 | 1683 | 34 |
| 1000 | 166833 | 334 |

### Verdict
**PASS.** The closed-form maximum, the location of the maximizer in the saturated branch,
the domination of the non-saturated branch, and the modular identity all hold for every
$n\le2000$ with no exception.

---
*This document reports an **independent computational verification** of the stated claims: each result was recomputed from scratch by a self-contained script (exact linear programming via SciPy/HiGHS for the fractional triangle-cover number, exact rational arithmetic for the integer optimization, and exhaustive enumeration of non-isomorphic graphs via the NetworkX atlas where indicated). This is computational evidence corroborating the analytic proof; it is not itself a formal proof. The machine-checked formal proof is the Lean development, which is conditiona