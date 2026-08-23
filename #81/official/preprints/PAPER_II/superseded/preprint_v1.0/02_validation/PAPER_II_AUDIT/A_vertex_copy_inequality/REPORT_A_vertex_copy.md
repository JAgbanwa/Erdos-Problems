---
geometry: margin=1in
fontsize: 11pt
---
# Independent Computational Verification
## Paper II — Section 3: the vertex-copy inequality (Lemma 3.1)

**Author of record:** Juan Pablo Traverso Gianini  **Date:** 2026-07-09  
**Artifact:** `A_vertex_copy_inequality/audit_A_vertex_copy.py`  **Verdict: PASS**

### Scope
Exhaustive over **all non-isomorphic graphs on 2–7 vertices** (NetworkX atlas), and for
**every** nonadjacent vertex pair $(u,v)$ in each graph.

### Claims verified
For nonadjacent $u,v$, writing $G_{v\to u}$ for the copy operation:

- **(I) Lemma 3.1:** $\Phi_\tau(G_{v\to u})+\Phi_\tau(G_{u\to v})\ge 2\,\Phi_\tau(G)$.
- **(II) eq. 3.4:** $e(G_{v\to u})+e(G_{u\to v})=2\,e(G)$ (exact).
- **(III) eq. 3.3:** $\tau_3^*(G_{v\to u})+\tau_3^*(G_{u\to v})\le 2\,\tau_3^*(G)$.
- **Cross-check:** $\tau_3^*(G)=\nu_3^*(G)$ (LP duality), computed by two independent LPs.

### Method
Python 3, NetworkX (graph atlas + chordality), SciPy `linprog` method=`highs`; exact `fractions` where noted. $\Phi_\tau(G)=|E(G)|-2\tau_3^*(G)$, with $\tau_3^*$ the optimum of the triangle-cover LP.

### Results
| $n$ | non-iso graphs | nonadjacent pairs tested |
|----|----|----|
| 2 | 2 | 1 |
| 3 | 4 | 6 |
| 4 | 11 | 33 |
| 5 | 34 | 170 |
| 6 | 156 | 1170 |
| 7 | 1044 | 10962 |

- Graphs tested: **1251**; nonadjacent pairs tested: **12342**; max $n$: **7**.
- Minimum slack of (I): **-7.11e-15** (numerically zero; inequality holds, attained with equality).
- Max absolute error of identity (II): **0.00e+00** (exact).
- Max violation of (III): **0.00e+00** (none).
- Max LP duality gap $|\tau_3^*-\nu_3^*|$: **2.66e-15**.
- **Violations: 0.** Runtime 142.24 s.

### Verdict
**PASS.** The vertex-copy inequality, both exact identities, and LP duality hold on the
entire enumerated universe with no violation. (Values at the $10^{-15}$ level are
floating-point noise.) This is the same $L1$ step machine-checked in the Lean development.

---
*This document reports an **independent computational verification** of the stated claims: each result was recomputed from scratch by a self-contained script (exact linear programming via SciPy/HiGHS for the fractional triangle-cover number, exact rational arithmetic for the integer optimization, and exhaustive enumeration of non-isomorphic graphs via the NetworkX atlas where indicated). This is computational evidence corroborating the analytic proof; it is not itself a formal proof. The machine-checked formal proof is the Lean development, which is conditio