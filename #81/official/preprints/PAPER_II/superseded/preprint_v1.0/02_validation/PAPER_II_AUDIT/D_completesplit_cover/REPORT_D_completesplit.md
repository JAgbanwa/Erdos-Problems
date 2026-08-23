---
geometry: margin=1in
fontsize: 11pt
---
# Independent Computational Verification
## Paper II — Section 6: the complete-split cover program (Prop 6.2, Cor 6.3, Lemma 6.1)

**Author of record:** Juan Pablo Traverso Gianini  **Date:** 2026-07-09  
**Artifact:** `D_completesplit_cover/audit_D_completesplit.py`  **Verdict: PASS**

### Scope
All complete-split graphs $S_{p,q}=K_p\vee\overline{K_q}$ with
$p\le 12$, $q\le 14$, $p+q\le 16$
— **139 cases**, including the degenerate $S_{2,0}$ and $p\le1$.

### Claims verified
- **(D1) Prop 6.2:** the full-graph LP value $\tau_3^*(S_{p,q})$ equals the closed form
  $0$ (if $p\le1$ or $(p,q)=(2,0)$), $\tfrac{\binom p2+pq}3$ (non-saturated $q\le p-1$, $p\ge3$),
  or $\binom p2$ (saturated $q\ge p-1$).
- **(D2) Cor 6.3:** $\Phi_\tau(S_{p,q})=|E|-2\tau_3^*$ equals $pq-\binom p2$ (saturated) or
  $\tfrac{\binom p2+pq}3$ (non-saturated).
- **(D3) Lemma 6.1:** the orbit-averaged 2-variable LP attains the **same** optimum as the full LP.

### Results (sample; full set in `results/summary.json`)
| $p$ | $q$ | $\tau_3^*$ formula | $\tau_3^*$ LP | $\Phi_\tau$ formula |
|----|----|----|----|----|
| 0 | 7 | 0.0 | 0.0 | 0.0 |
| 0 | 8 | 0.0 | 0.0 | 0.0 |
| 0 | 9 | 0.0 | 0.0 | 0.0 |
| 0 | 10 | 0.0 | 0.0 | 0.0 |
| 0 | 11 | 0.0 | 0.0 | 0.0 |
| 0 | 12 | 0.0 | 0.0 | 0.0 |
| 0 | 13 | 0.0 | 0.0 | 0.0 |
| 0 | 14 | 0.0 | 0.0 | 0.0 |
| 1 | 0 | 0.0 | 0.0 | 0.0 |
| 1 | 1 | 0.0 | 0.0 | 1.0 |
| 1 | 2 | 0.0 | 0.0 | 2.0 |
| 1 | 3 | 0.0 | 0.0 | 3.0 |

- D1 (LP = formula) violations: **0**.
- D2 ($\Phi_\tau$ formula) violations: **0**.
- D3 (orbit-LP = full LP) violations: **0**.
- **All 139 cases exact** (agreement to LP tolerance $10^{-7}$). Runtime 0.58 s.

### Verdict
**PASS.** The piecewise cover formula, the $\Phi_\tau$ values, and the sufficiency of
orbit averaging are confirmed exactly across the tested range.

---
*This document reports an **independent computational verification** of the stated claims: each result was recomputed from scratch by a self-contained script (exact linear programming via SciPy/HiGHS for the fractional triangle-cover number, exact rational arithmetic for the integer optimization, and exhaustive enumeration of non-isomorphic graphs via the NetworkX atlas where indicated). This is computational evidence corroborating the analytic proof; it is not itself a formal proof. The machine-checked formal proof is the Lean development, which is conditi